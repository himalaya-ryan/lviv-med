#! /usr/bin/python

###############################################################################
# Copyright (c) 2008-2024 Broadcom. All Rights Reserved.
# Broadcom Confidential. The term "Broadcom" refers to Broadcom Inc.
# and/or its subsidiaries.
#
# This file is part of Weasel.
#
# Weasel is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License
# version 2 for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51
# Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
#

# autotest: doctest

import json
import sys
import operator
import os
import optparse
import re
import socket
import shutil
import tempfile
import tarfile

import esxclipy
import vmkctl

TASKNAME = 'Precheck'
TASKDESC = 'Preliminary checks'

# Directory where this file is running. Script expects data files, helper
# utilities to exist here.
SCRIPT_DIR = os.path.abspath(os.path.dirname(__file__))

# Import the correct esximage modules for the use case.
# 1) VUM: esximage of the upgrade image is in esximage.zip next to this script.
# 2) VLCM/esxcli: this script is imported by the new esximage in /tmp with the
#    site-packages/vmware folder already in import paths.
# 3) ISO installer: should use the default vmware.esximage package.
# For 1/2, since vmware module is commutable, to avoid importing the old
# esximage on the host via vmware.esximage, import from inside the vmware
# folder instead.
esximageZip = os.path.join(SCRIPT_DIR, "esximage.zip")
if os.path.exists(esximageZip):
   sys.path.insert(0, esximageZip)
   sys.path.insert(0, os.path.join(esximageZip, 'vmware'))

try:
   # VUM, esxcli and VLCM
   from esximage import (Bulletin, Database, Errors, HostImage, Metadata,
                         ImageProfile, Scan, Version, Vib, VibCollection)
   from esximage.Installer import InstallerCommon
   from esximage.Installer import (BootBankInstaller, LiveImageInstaller,
                                   LockerInstaller)
   from esximage.Utils import HostInfo
   from esximage.Utils.Misc import byteToStr
except ImportError:
   # ISO Installer
   from vmware.esximage import (Bulletin, Database, Errors, HostImage, Metadata,
                                ImageProfile, Scan, Version, Vib, VibCollection)
   from vmware.esximage.Installer import InstallerCommon
   from vmware.esximage.Installer import (BootBankInstaller, LiveImageInstaller,
                                          LockerInstaller)
   from vmware.esximage.Utils import HostInfo
   from vmware.esximage.Utils.Misc import byteToStr

from esxutils import EsxcliError, runCli
from vmware.runcommand import runcommand, RunCommandError


# the new ramdisk (resource pool) where we will copy the ISO to
RAMDISK_NAME = '/upgrade_scratch'

ESX_CONF_PATH = '/etc/vmware/esx.conf'
ESXI_PRODUCT = 'VMware ESXi'

# Path of the vmklinux module, absence of it means the image supports native
# drivers only.
VMKLINUX_MOD_PATH = 'usr/lib/vmware/vmkmod/vmklinux_9'

try:
    import logging
    log = logging.getLogger('upgrade_precheck')
except ImportError:
    class logger:
        def write(self, *args):
            sys.stderr.write(args[0] % args[1:])
            sys.stderr.write("\n")
        debug = write
        error = write
        info = write
        warn = write
        warning = write
        def log(self, level, *args):
            sys.stderr.write(*args)
    log = logger()

SIZE_MiB = 1024 * 1024

class Result:
    ERROR = "ERROR"
    WARNING = "WARNING"
    OVERRIDEWARNING = "OVERRIDEWARNING"
    SUCCESS = "SUCCESS"

    def __init__(self, name, found, expected,
                 comparator=operator.eq, errorMsg="", mismatchCode=None):
        """Parameters:
              * name         - A string, giving the name of the test.
              * found        - An object or sequence of objects. Each object
                               will be converted to a string representation, so
                               the objects should return an appropriate value
                               via their __str__() method.
              * expected     - Follows the same conventions as the found
                               parameter, but represents the result(s) that the
                               test expected.
              * comparator   - A method use to compare the found and expected
                               parameters. If comparator(found, expected) is
                               True, the value of the object's code attribute
                               will be Result.SUCCESS. Otherwise, the value of
                               the mismatchCode is returned, if specified, or
                               Result.ERROR.
              * errorMsg     - A string, describing the error.
              * mismatchCode - If not None, specifies a code to be assigned to
                               this object's result attribute when
                               comparator(found, expected) is False.
        """
        if not mismatchCode:
            mismatchCode = Result.ERROR

        self.name = name
        self.found = found
        self.expected = expected
        self.errorMsg = errorMsg
        if comparator(self.found, self.expected):
            self.code = Result.SUCCESS
        else:
            self.code = mismatchCode

    def __nonzero__(self):
        """For python2"""
        return self.code == Result.SUCCESS

    def __bool__(self):
        """For python3"""
        return self.__nonzero__()

    def __str__(self):
        if self.name == "MEMORY_SIZE":
            return ('<%s %s: This host has %s of RAM. %s are needed>'
                    % (self.name, self.code,
                     formatValue(self.found[0]), formatValue(self.expected[0])))
        elif self.name == "SPACE_AVAIL_ISO":
            return ('<%s %s: Only %s available for ISO files. %s are needed>'
                    % (self.name, self.code,
                     formatValue(self.found[0]), formatValue(self.expected[0])))
        elif self.name == "UNSUPPORTED_DEVICES":
            return ('<%s %s: This host has unsupported devices %s>'
                    % (self.name, self.code, self.found))
        elif self.name == "CPU_CORES":
            return ('<%s %s: This host has %s cpu core(s) which is less '
                   'than recommended %s cpu cores>'
                    % (self.name, self.code, self.found, self.expected))
        elif self.name == "HARDWARE_VIRTUALIZATION":
            return ('<%s %s: Hardware Virtualization is not a '
                   'feature of the CPU, or is not enabled in the BIOS>'
                    % (self.name, self.code))
        elif self.name == "VALIDATE_HOST_HW":
            # Prepare the strings.
            prepStrings = []
            for match, vibPlat, hostPlat in self.found:
                hostStr = "%s VIB for %s found, but host is %s" % \
                          (match, vibPlat, hostPlat)
                prepStrings.append(hostStr)

            return '<%s %s: %s>' % (self.name, self.code,
                                    ', '.join(prepStrings))
        elif self.name == "CONFLICTING_VIBS":
            return ('<%s %s: %s %s>'
                    % (self.name, self.code, self.errorMsg, self.found))
        elif self.name == "IMAGEPROFILE_SIZE":
            return ('<%s %s: %s: '
                    'Target image profile size is %s MB,  but maximum '
                    'supported size is %s MB>'
                    % (self.name, self.code, self.errorMsg,
                       self.found, self.expected))
        elif self.name == "LOCKER_SPACE_AVAIL":
            return ('<%s %s: %s: '
                    'Target version supports boot disks that are at least '
                    '%u MB, but the boot disk has %u MB>'
                    % (self.name, self.code, self.errorMsg,
                       self.expected, self.found))
        elif self.name in ("UPGRADE_PATH",  "CPU_SUPPORT", "VMFS_VERSION",
                           "LIMITED_DRIVERS", "BOOT_DISK_SIZE", "TPM_VERSION",
                           "EXTRA_CPU_LICENSE", "CVDS_MIGRATION_READINESS",
                           "SPHERELET_VERSION", "SHA1_CERT", "ENTROPY_CACHE",
                           "BIOS_FIRMWARE_TYPE", "VFAT_CORRUPTION"):
            return ('<%s %s: %s>'
                    % (self.name, self.code, self.errorMsg))
        elif self.name == "DPU_MANAGED":
            return ('<%s %s: %s, '
                    'Host managing DPU(s) is not supported by vum cluster>'
                    % (self.name, self.code, self.errorMsg))
        else:
            return ('<%s %s: Found=%s Expected=%s %s>'
                    % (self.name, self.code,
                       self.found, self.expected, self.errorMsg))
    __repr__ = __str__

    def isWarnType(self):
        ''' This is used to check if result code is of warning type.
        WARNING and OVERRIDEWARNING both code used for warning type only.
        '''
        return self.code in (Result.WARNING, Result.OVERRIDEWARNING)

class PciInfo:
    '''Class to encapsulate PCI data'''
    #
    # TODO: this technique probably won't be sufficient.  I'll need to
    #       check the subdevice info as well.  The easy approach is probably
    #       to import pciidlib.py and extend it with these __eq__ and __ne__
    #       functions.  Also, I'll have to check that pciidlib works on both
    #       ESX and ESXi
    #

    def __init__(self, vendorId, deviceId, subsystem=None, description=""):
        '''Construct a PciInfo object with the given values: vendorId and
        deviceId should be strings with the appropriate hex values.  Description
        is an english description of the PCI device.'''

        self.vendorId = vendorId.lower()
        self.deviceId = deviceId.lower()
        if subsystem:
            self.subsystem = subsystem.lower()
        else:
            self.subsystem = subsystem
        self.description = description

    # XXX WARNING: The 'ne' operator is wider than 'eq' operator.  Note that
    # 'ne' explitcly compares all properties for inequality.  Equality will only
    # compare the vendorId and deviceId if any of the inputs don't define a
    # subsystem.
    def __eq__(self, rhs):
        if self.subsystem is None or rhs.subsystem is None:
            return (self.vendorId == rhs.vendorId and
                    self.deviceId == rhs.deviceId)
        else:
            return (self.vendorId == rhs.vendorId and
                    self.deviceId == rhs.deviceId and
                    self.subsystem == rhs.subsystem)

    def __ne__(self, rhs):
        return (self.vendorId != rhs.vendorId or
                self.deviceId != rhs.deviceId or
                self.subsystem != rhs.subsystem)

    def __str__(self):
        return "%s [%s:%s %s]" % (self.description, self.vendorId,
                                  self.deviceId, self.subsystem)

    def __repr__(self):
        return "<PciInfo '%s'>" % str(self)

VMKLINUX_UNSUPPORTED_PCI_DEVICE_LIST = [
    # Devices that are deprecated because of VMKLinux removal.
    # e.g. e1000 - PciInfo("8086", "1075", None, "82547GI Gigabit Ethernet Controller")
    # aacraid
    PciInfo("1011", "0046", "103c:10c2", "Hewlett-Packard NetRAID-4M"),
    PciInfo("1011", "0046", "9005:0364", "AAC-364 (Adaptec 5400S)"),
    PciInfo("1011", "0046", "9005:0365", "Adaptec 5400S"),
    PciInfo("1011", "0046", "9005:1364", "Dell PowerEdge RAID Controller 2"),
    PciInfo("1011", "0046", "9005:1365", "Dell PowerEdge RAID Controller 2"),
    PciInfo("1028", "0001", "1028:0001", "PowerEdge Expandable RAID Controller 2/Si"),
    PciInfo("1028", "0002", "1028:0002", "PowerEdge Expandable RAID Controller 3/Di"),
    PciInfo("1028", "0002", "1028:00d1", "PowerEdge Expandable RAID Controller 3/Di"),
    PciInfo("1028", "0002", "1028:00d9", "PowerEdge Expandable RAID Controller 3/Di"),
    PciInfo("1028", "0003", "1028:0003", "PowerEdge Expandable RAID Controller 3/Si"),
    PciInfo("1028", "0004", "1028:00d0", "PowerEdge Expandable RAID Controller 3/Si"),
    PciInfo("1028", "000a", "1028:0106", "PowerEdge Expandable RAID Controller 3/Di"),
    PciInfo("1028", "000a", "1028:011b", "PowerEdge Expandable RAID Controller 3/Di 1650"),
    PciInfo("1028", "000a", "1028:0121", "PowerEdge Expandable RAID Controller 3/Di 2650"),
    PciInfo("9005", "0200", "0900:0200", "Themisto Jupiter Platform"),
    PciInfo("9005", "0283", "9005:0283", "Catapult"),
    PciInfo("9005", "0284", "9005:0284", "Tomcat"),
    PciInfo("9005", "0285", None       , "Adaptec SCSI"),
    PciInfo("9005", "0285", "1014:02f2", "ServeRAID 8i"),
    PciInfo("9005", "0285", "1028:0287", "Perc 320/DC"),
    PciInfo("9005", "0285", "1028:0291", "CERC SATA RAID 2 PCI SATA 6ch (DellCosair)"),
    PciInfo("9005", "0285", "103c:3227", "AAR-2610SA PCI SATA 6ch"),
    PciInfo("9005", "0285", "17aa:0286", "Legend S220"),
    PciInfo("9005", "0285", "17aa:0287", "Legend S230"),
    PciInfo("9005", "0285", "9005:0285", "2200S Vulcan"),
    PciInfo("9005", "0285", "9005:0286", "2120S Crusader"),
    PciInfo("9005", "0285", "9005:0287", "2200S Vulcan-2m"),
    PciInfo("9005", "0285", "9005:0288", "Adaptec 3230S"),
    PciInfo("9005", "0285", "9005:0289", "Adaptec 3240S"),
    PciInfo("9005", "0285", "9005:028a", "ASR-2020ZCR SCSI PCI-X ZCR"),
    PciInfo("9005", "0285", "9005:028b", "ASR-2025ZCR SCSI SO-DIMM PCI-X ZCR"),
    PciInfo("9005", "0285", "9005:028e", "ASR-2020SA SATA PCI-X ZCR"),
    PciInfo("9005", "0285", "9005:028f", "ASR-2025SA SATA SO-DIMM PCI-X ZCR"),
    PciInfo("9005", "0285", "9005:0290", "AAR-2410SA PCI SATA 4ch"),
    PciInfo("9005", "0285", "9005:0292", "AAR-2810SA PCI SATA 8ch"),
    PciInfo("9005", "0285", "9005:0293", "AAR-21610SA PCI SATA 16ch"),
    PciInfo("9005", "0285", "9005:0294", "ESD SO-DIMM PCI-X SATA ZCR"),
    PciInfo("9005", "0285", "9005:0296", "ASR-2240S"),
    PciInfo("9005", "0285", "9005:0297", "ASR-4005SAS"),
    PciInfo("9005", "0285", "9005:0298", "ASR-4000SAS"),
    PciInfo("9005", "0285", "9005:0299", "ASR-4800SAS"),
    PciInfo("9005", "0285", "9005:029a", "ASR-4800SAS"),
    PciInfo("9005", "0285", "9005:02a4", "ICP9085LI"),
    PciInfo("9005", "0285", "9005:02a5", "ICP5085BR"),
    PciInfo("9005", "0286", None       , "Adaptec Rocket"),
    PciInfo("9005", "0286", "1014:9540", "ServeRAID 8k/8k-l4"),
    PciInfo("9005", "0286", "1014:9580", "ServeRAID 8k/8k-l8"),
    PciInfo("9005", "0286", "9005:028c", "ASR-2230S + ASR-2230SLP PCI-X"),
    PciInfo("9005", "0286", "9005:028d", "ASR-2130S"),
    PciInfo("9005", "0286", "9005:029b", "AAR-2820SA"),
    PciInfo("9005", "0286", "9005:029c", "AAR-2620SA"),
    PciInfo("9005", "0286", "9005:029d", "AAR-2420SA"),
    PciInfo("9005", "0286", "9005:029e", "ICP9024R0"),
    PciInfo("9005", "0286", "9005:029f", "ICP9014R0"),
    PciInfo("9005", "0286", "9005:02a0", "ICP9047MA"),
    PciInfo("9005", "0286", "9005:02a1", "ICP9087MA"),
    PciInfo("9005", "0286", "9005:02a2", "ASR-4810SAS"),
    PciInfo("9005", "0286", "9005:02a3", "ICP5085AU"),
    PciInfo("9005", "0286", "9005:02a6", "ICP9067MA"),
    PciInfo("9005", "0286", "9005:0800", "Callisto Jupiter Platform"),
    PciInfo("9005", "0287", "9005:0800", "Themisto Jupiter Platform"),
    # adp94xx
    PciInfo("9005", "8017", None       , "AHA-29320ALP"),
    # bnx2x
    PciInfo("14e4", "164e", None       , "NetXtreme II BCM57710 10 Gigabit Ethernet"),
    PciInfo("14e4", "164f", None       , "NetXtreme II BCM57711 10 Gigabit Ethernet"),
    PciInfo("14e4", "1650", None       , "NetXtreme II BCM57711E 10 Gigabit Ethernet"),
    PciInfo("14e4", "1650", "103c:171c", "NetXtreme II BCM57711E/NC532m 10 Gigabit Ethernet"),
    PciInfo("14e4", "1650", "103c:7058", "NetXtreme II BCM57711E/NC532i 10 Gigabit Ethernet"),
    # e1000
    PciInfo("8086", "1000", None       , "82542 Gigabit Ethernet Controller"),
    PciInfo("8086", "100f", None       , "82545EM Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "1010", None       , "82546EB Gigabit Ethernet Controller (Copper)"),
    # igb
    PciInfo("8086", "0438", None       , "DH8900CC Series Gigabit Network Connection"),
    PciInfo("8086", "043a", None       , "DH8900CC Series Gigabit Fiber Network Connection"),
    PciInfo("8086", "043c", None       , "DH8900CC Series Gigabit Backplane Network Connection"),
    PciInfo("8086", "0440", None       , "DH8900CC Series Gigabit SFP Network Connection"),
    PciInfo("8086", "10a7", None       , "82575EB Gigabit Network Connection"),
    PciInfo("8086", "10a9", None       , "82575EB Gigabit Backplane Connection"),
    PciInfo("8086", "10c9", None       , "82576 Gigabit Network Connection"),
    PciInfo("8086", "10d6", None       , "82575GB Gigabit Network Connection"),
    PciInfo("8086", "10e6", None       , "82576 Gigabit Network Connection"),
    PciInfo("8086", "10e7", None       , "82576 Gigabit Network Connection"),
    PciInfo("8086", "10e8", None       , "82576 Gigabit Network Connection"),
    PciInfo("8086", "150a", None       , "82576NS Gigabit Network Connection"),
    PciInfo("8086", "150d", None       , "82576 Gigabit Backplane Connection"),
    PciInfo("8086", "1518", None       , "82576NS SerDes Gigabit Network Connection"),
    PciInfo("8086", "1526", None       , "82576 Gigabit Network Connection"),
    PciInfo("8086", "1534", None       , "I210 Gigabit Network Connection"),
    PciInfo("8086", "1535", None       , "I210 Gigabit Network Connection"),
    # ixgbe
    PciInfo("8086", "10b6", None       , "82598 10GbE PCI-Express Ethernet Controller"),
    PciInfo("8086", "10c6", None       , "82598EB 10-Gigabit AF Dual Port Network Connection"),
    PciInfo("8086", "10c7", None       , "82598EB 10-Gigabit AF Network Connection"),
    PciInfo("8086", "10c8", None       , "82598EB 10-Gigabit AT Network Connection"),
    PciInfo("8086", "10db", None       , "82598EB 10-Gigabit Dual Port Network Connection"),
    PciInfo("8086", "10dd", None       , "82598EB 10-Gigabit AT CX4 Network Connection"),
    PciInfo("8086", "10e1", None       , "82598EB 10-Gigabit AF Dual Port Network Connection"),
    PciInfo("8086", "10ec", None       , "82598EB 10-Gigabit AT CX4 Network Connection"),
    PciInfo("8086", "10f1", None       , "82598EB 10-Gigabit AF Dual Port Network Connection"),
    PciInfo("8086", "10f4", None       , "82598EB 10-Gigabit AF Network Connection"),
    PciInfo("8086", "1508", None       , "82598EB Gigabit BX Network Connection"),
    PciInfo("8086", "150b", None       , "82598EB 10-Gigabit AT2 Server Adapter"),
    PciInfo("8086", "1529", None       , "82599 10 Gigabit Dual Port Backplane Connection with FCoE"),
    PciInfo("8086", "152a", None       , "82599 10 Gigabit Dual port Network Connection with FCoE"),
    PciInfo("8086", "154f", None       , "82599EB 10Gigabit Dual Port Network Connection"),
    # megaraid_mbox
    PciInfo("1000", "0409", "1000:3004", "LSI Logic MegaRAID SATA 300-4XLP SATA II RAID Adapter"),
    PciInfo("1000", "0409", "1000:3008", "LSI Logic MegaRAID SATA 300-8XLP SATA II RAID Adapter"),
    # megaraid_sas
    PciInfo("1000", "0060", "1028:1f0a", "Dell PERC 6/E Adapter"),
    PciInfo("1000", "0060", "1028:1f0b", "Dell PERC 6/i Adapter"),
    PciInfo("1000", "0060", "1028:1f0c", "Dell PERC 6/i Integrated"),
    PciInfo("1000", "0060", "1028:1f0d", "Dell PERC 6/i Integrated Blade"),
    PciInfo("1000", "0060", "1028:1f11", "Dell PERC 6/i Integrated"),
    PciInfo("1000", "0071", None       , "MegaRAID SAS GEN2 SKINNY Controller"),
    PciInfo("1000", "0073", "1028:1f4f", "PERC H310 Integrated"),
    PciInfo("1000", "0073", "1028:1f54", "PERC H310 Reserved"),
    PciInfo("1000", "0073", None       , "MegaRAID SAS SKINNY Controller"),
    PciInfo("1000", "0078", None       , "MegaRAID SAS GEN2 Controller"),
    PciInfo("1000", "0079", None       , "MegaRAID SAS GEN2 Controller"),
    PciInfo("1000", "0079", "1028:1f15", "Dell PERC H800 Adapter"),
    PciInfo("1000", "0079", "1028:1f16", "Dell PERC H700 Adapter"),
    PciInfo("1000", "0079", "1028:1f17", "Dell PERC H700 Integrated"),
    PciInfo("1000", "0079", "1028:1f18", "Dell PERC H700 Modular"),
    PciInfo("1000", "0079", "1028:1f19", "Dell PERC H700 / PERC 800"),
    PciInfo("1000", "0079", "1028:1f1a", "Dell PERC H700 / PERC 800"),
    PciInfo("1000", "0079", "1028:1f1b", "Dell PERC H700 / PERC 800"),
    PciInfo("1000", "007c", None       , "MegaRAID SAS 1078 Controller"),
    PciInfo("1000", "0408", "1028:0002", "Dell PERC 4e/DC Adapter"),
    PciInfo("1000", "0411", None       , "LSI MegaRAID SAS1064R"),
    PciInfo("1000", "0413", None       , "LSI MegaRAID SAS1064"),
    PciInfo("1000", "1960", "1028:0518", "Dell PERC 4/DC"),
    PciInfo("1028", "0015", None       , "PowerEdge Expandable RAID Controller 5"),
    # mlx4_core
    PciInfo("15b3", "0191", None       , "MT25408 [ConnectX IB SDR Flash Recovery]"),
    PciInfo("15b3", "1002", None       , "MT25400 Family [ConnectX-2 Virtual Function]"),
    PciInfo("15b3", "1005", None       , "MT27510 Family"),
    PciInfo("15b3", "1006", None       , "MT27511 Family"),
    PciInfo("15b3", "1008", None       , "MT27521 Family"),
    PciInfo("15b3", "1009", None       , "MT27530 Family"),
    PciInfo("15b3", "100a", None       , "MT27531 Family"),
    PciInfo("15b3", "100b", None       , "MT27540 Family"),
    PciInfo("15b3", "100c", None       , "MT27541 Family"),
    PciInfo("15b3", "100d", None       , "MT27550 Family"),
    PciInfo("15b3", "100e", None       , "MT27551 Family"),
    PciInfo("15b3", "100f", None       , "MT27560 Family"),
    PciInfo("15b3", "1010", None       , "MT27561 Family"),
    PciInfo("15b3", "6340", None       , "MT25408 [ConnectX VPI - 10GigE / IB SDR]"),
    PciInfo("15b3", "634a", None       , "MT25418 [ConnectX VPI - 10GigE / IB DDR, PCIe 2.0 2.5GT/s]"),
    PciInfo("15b3", "6368", None       , "MT25448 [ConnectX EN 10GigE, PCIe 2.0 2.5GT/s]"),
    PciInfo("15b3", "6372", None       , "MT25408 [ConnectX EN 10GigE 10BASE-T, PCIe 2.0 2.5GT/s]"),
    PciInfo("15b3", "6732", None       , "MT26418 [ConnectX VPI - 10GigE / IB DDR, PCIe 2.0 5GT/s]"),
    PciInfo("15b3", "673c", None       , "MT26428 [ConnectX VPI - 10GigE / IB QDR, PCIe 2.0 5GT/s]"),
    PciInfo("15b3", "6746", None       , "MT26438 [ConnectX VPI PCIe 2.0 5GT/s - IB QDR / 10GigE Virtualization+]"),
    PciInfo("15b3", "6750", None       , "MT26448 [ConnectX EN 10GigE , PCIe 2.0 5GT/s]"),
    PciInfo("15b3", "675a", None       , "MT25408 [ConnectX EN 10GigE 10GBaseT, PCIe Gen2 5GT/s]"),
    PciInfo("15b3", "6764", None       , "MT26468 [ConnectX EN 10GigE, PCIe 2.0 5GT/s Virtualization+]"),
    PciInfo("15b3", "676e", None       , "MT26488 [ConnectX VPI PCIe 2.0 5GT/s - IB DDR / 10GigE Virtualization+]"),
    PciInfo("15b3", "6778", None       , "MT26488 [ConnectX VPI PCIe 2.0 5GT/s - IB DDR / 10GigE Virtualization+]"),
    # mpt2sas
    PciInfo("1000", "0050", None       , "LSI1064"),
    PciInfo("1000", "0054", "1028:1f04", "Dell SAS 5/E Adapter"),
    PciInfo("1000", "0054", "1028:1f06", "Dell SAS 5/i Integrated"),
    PciInfo("1000", "0054", "1028:1f07", "Dell SAS 5/iR Integrated"),
    PciInfo("1000", "0054", "1028:1f09", "Dell SAS 5/iR Adapter"),
    PciInfo("1000", "0054", None       , "LSI1068"),
    PciInfo("1000", "0056", None       , "LSI1064E"),
    PciInfo("1000", "0058", "1028:021d", "Dell SAS 6/iR Integrated"),
    PciInfo("1000", "0058", "1028:1f0e", "Dell SAS 6/iR Adapter"),
    PciInfo("1000", "0058", "1028:1f0f", "Dell SAS 6/iR Integrated"),
    PciInfo("1000", "0058", "1028:1f10", "Dell SAS 6/iR Integrated"),
    PciInfo("1000", "0058", None       , "LSI1068E"),
    PciInfo("1000", "005a", None       , "LSI1066E"),
    PciInfo("1000", "005c", None       , "LSI1064A"),
    PciInfo("1000", "005e", None       , "LSI1066"),
    PciInfo("1000", "0062", None       , "LSI1078"),
    PciInfo("1000", "0064", None       , "LSI2116_1"),
    PciInfo("1000", "0065", None       , "LSI2116_2"),
    PciInfo("1000", "0070", None       , "LSI2004"),
    PciInfo("1000", "0070", "1590:0046", "HP H210i Host Bus Adapter"),
    PciInfo("1000", "0072", None       , "LSI2008"),
    PciInfo("1000", "0072", "1028:1f1c", "Dell 6Gbps SAS HBA Adapter"),
    PciInfo("1000", "0072", "1028:1f1d", "Dell PERC H200 Adapter"),
    PciInfo("1000", "0072", "1028:1f1e", "Dell PERC H200 Integrated"),
    PciInfo("1000", "0072", "1028:1f1f", "Dell PERC H200 Modular"),
    PciInfo("1000", "0072", "1028:1f20", "Dell PERC H200 Embedded"),
    PciInfo("1000", "0072", "1028:1f21", "Dell PERC H200"),
    PciInfo("1000", "0072", "1028:1f22", "Dell 6Gbps SAS HBA"),
    PciInfo("1000", "0072", "8086:3700", "Intel(R) SSD 910 Series"),
    PciInfo("1000", "0074", None       , "LSI2108_1"),
    PciInfo("1000", "0076", None       , "LSI2108_2"),
    PciInfo("1000", "0077", None       , "LSI2108_3"),
    PciInfo("1000", "007e", None       , "LSI WarpDrive SSD"),
    # mptspi
    PciInfo("1000", "0030", None       , "53c1030 PCI-X Fusion-MPT Dual Ultra320 SCSI"),
    PciInfo("1000", "0032", None       , "53c1035 PCI-X Fusion-MPT Dual Ultra320 SCSI"),
    PciInfo("1000", "0621", None       , "FC909"),
    PciInfo("1000", "0622", None       , "FC929"),
    PciInfo("1000", "0624", None       , "FC919"),
    PciInfo("1000", "0626", None       , "FC929X"),
    PciInfo("1000", "0628", None       , "FC919X"),
    # pata_atiixp
    PciInfo("1002", "439c", None       , "SB700/SB800 IDE Controller"),
    PciInfo("1022", "780c", None       , "AMD Hudson IDE Controller"),
    # tg3
    PciInfo("14e4", "1600", None       , "NetXtreme BCM5752 Gigabit Ethernet"),
    PciInfo("14e4", "1601", None       , "NetXtreme BCM5752M Gigabit Ethernet"),
    PciInfo("14e4", "1641", None       , "NetXtreme BCM57787 Gigabit Ethernet"),
    PciInfo("14e4", "1642", None       , "NetXtreme BCM57764 Gigabit Ethernet"),
    PciInfo("14e4", "1644", None       , "NetXtreme BCM5700 Gigabit Ethernet"),
    PciInfo("14e4", "1645", None       , "NetXtreme BCM5701 Gigabit Ethernet"),
    PciInfo("14e4", "1646", None       , "NetXtreme BCM5702 Gigabit Ethernet"),
    PciInfo("14e4", "1647", None       , "NetXtreme BCM5703 Gigabit Ethernet"),
    PciInfo("14e4", "1648", None       , "NetXtreme BCM5704 Gigabit Ethernet"),
    PciInfo("14e4", "1649", None       , "NetXtreme BCM5704S Gigabit Ethernet"),
    PciInfo("14e4", "164d", None       , "NetXtreme BCM5702FE Gigabit Ethernet"),
    PciInfo("14e4", "1653", None       , "NetXtreme BCM5705 Gigabit Ethernet"),
    PciInfo("14e4", "1654", None       , "NetXtreme BCM5705 Gigabit Ethernet"),
    PciInfo("14e4", "1659", None       , "NetXtreme BCM5721 Gigabit Ethernet"),
    PciInfo("14e4", "165a", None       , "NetXtreme BCM5722 Gigabit Ethernet"),
    PciInfo("14e4", "165b", None       , "NetXtreme BCM5723 Gigabit Ethernet"),
    PciInfo("14e4", "165c", None       , "NetXtreme BCM5724 Gigabit Ethernet"),
    PciInfo("14e4", "165d", None       , "NetXtreme BCM5705M Gigabit Ethernet"),
    PciInfo("14e4", "165e", None       , "NetXtreme BCM5705M Gigabit Ethernet"),
    PciInfo("14e4", "1668", None       , "NetXtreme BCM5714 Gigabit Ethernet"),
    PciInfo("14e4", "1669", None       , "NetXtreme BCM5714S Gigabit Ethernet"),
    PciInfo("14e4", "166a", None       , "NetXtreme BCM5780 Gigabit Ethernet"),
    PciInfo("14e4", "166b", None       , "NetXtreme BCM5780S Gigabit Ethernet"),
    PciInfo("14e4", "166e", None       , "NetXtreme BCM5705F Fast Ethernet"),
    PciInfo("14e4", "1672", None       , "NetXtreme BCM5754M Gigabit Ethernet"),
    PciInfo("14e4", "1673", None       , "NetXtreme BCM5755M Gigabit Ethernet"),
    PciInfo("14e4", "1674", None       , "NetXtreme BCM5756ME Gigabit Ethernet"),
    PciInfo("14e4", "1677", None       , "NetXtreme BCM5751 Gigabit Ethernet"),
    PciInfo("14e4", "1678", "103c:703e", "NC326i PCIe Dual Port Gigabit Server Adapter"),
    PciInfo("14e4", "1678", None       , "NetXtreme BCM5715 Gigabit Ethernet"),
    PciInfo("14e4", "1679", None       , "NetXtreme BCM5715S Gigabit Ethernet"),
    PciInfo("14e4", "167a", None       , "NetXtreme BCM5754 Gigabit Ethernet"),
    PciInfo("14e4", "167b", None       , "NetXtreme BCM5755 Gigabit Ethernet"),
    PciInfo("14e4", "167d", None       , "NetXtreme BCM5751M Gigabit Ethernet"),
    PciInfo("14e4", "167e", None       , "NetXtreme BCM5751F Fast Ethernet"),
    PciInfo("14e4", "167f", None       , "NetLink BCM5787F Fast Ethernet"),
    PciInfo("14e4", "1680", None       , "NetXtreme BCM5761e Gigabit Ethernet"),
    PciInfo("14e4", "1681", None       , "NetXtreme BCM5761 Gigabit Ethernet"),
    PciInfo("14e4", "1683", None       , "NetXtreme BCM57767 Gigabit Ethernet"),
    PciInfo("14e4", "1684", None       , "NetXtreme BCM5764M Gigabit Ethernet"),
    PciInfo("14e4", "1687", None       , "NetXtreme BCM5762 Gigabit Ethernet"),
    PciInfo("14e4", "1688", None       , "NetXtreme BCM5761S Gigabit Ethernet"),
    PciInfo("14e4", "1689", None       , "NetXtreme BCM5761SE Gigabit Ethernet"),
    PciInfo("14e4", "1690", None       , "NetXtreme BCM57760 Gigabit Ethernet"),
    PciInfo("14e4", "1691", None       , "NetLink BCM57788 Gigabit Ethernet"),
    PciInfo("14e4", "1692", None       , "NetLink BCM57780 Gigabit Ethernet"),
    PciInfo("14e4", "1693", None       , "NetLink BCM5787M Gigabit Ethernet"),
    PciInfo("14e4", "1694", None       , "NetLink BCM57790 Fast Ethernet"),
    PciInfo("14e4", "1696", None       , "NetXtreme BCM5782 Gigabit Ethernet"),
    PciInfo("14e4", "1698", None       , "NetLink BCM5784M Gigabit Ethernet"),
    PciInfo("14e4", "1699", None       , "NetLink BCM5785 Gigabit Ethernet"),
    PciInfo("14e4", "169a", None       , "NetLink BCM5786 Gigabit Ethernet"),
    PciInfo("14e4", "169b", None       , "NetLink BCM5787 Gigabit Ethernet"),
    PciInfo("14e4", "169c", None       , "NetXtreme BCM5788 Gigabit Ethernet"),
    PciInfo("14e4", "169d", None       , "NetLink BCM5789 Gigabit Ethernet"),
    PciInfo("14e4", "16a0", None       , "NetLink BCM5785 Fast Ethernet"),
    PciInfo("14e4", "16a6", None       , "NetXtreme BCM5702 Gigabit Ethernet"),
    PciInfo("14e4", "16a7", None       , "NetXtreme BCM5703 Gigabit Ethernet"),
    PciInfo("14e4", "16a8", None       , "NetXtreme BCM5704S Gigabit Ethernet"),
    PciInfo("14e4", "16b0", None       , "NetXtreme BCM57761 Gigabit Ethernet"),
    PciInfo("14e4", "16b1", None       , "NetXtreme BCM57781 Gigabit Ethernet"),
    PciInfo("14e4", "16b2", None       , "NetXtreme BCM57791 Gigabit Ethernet"),
    PciInfo("14e4", "16b4", None       , "NetXtreme BCM57765 Gigabit Ethernet"),
    PciInfo("14e4", "16b5", None       , "NetXtreme BCM57785 Gigabit Ethernet"),
    PciInfo("14e4", "16b6", None       , "NetXtreme BCM57795 Gigabit Ethernet"),
    PciInfo("14e4", "16c6", None       , "NetXtreme BCM5702A3 Gigabit Ethernet"),
    PciInfo("14e4", "16c7", None       , "NetXtreme BCM5703 Gigabit Ethernet"),
    PciInfo("14e4", "16dd", None       , "NetLink BCM5781 Gigabit Ethernet"),
    PciInfo("14e4", "16f7", None       , "NetXtreme BCM5753 Gigabit Ethernet"),
    PciInfo("14e4", "16fd", None       , "NetXtreme BCM5753M Gigabit Ethernet"),
    PciInfo("14e4", "16fe", None       , "NetXtreme BCM5753F Fast Ethernet"),
    PciInfo("14e4", "170d", None       , "NetXtreme BCM5901 100Base-TX"),
    PciInfo("14e4", "170e", None       , "NetXtreme BCM5901 100Base-TX"),
    PciInfo("14e4", "1712", None       , "NetLink BCM5906 Fast Ethernet"),
    PciInfo("14e4", "1713", None       , "NetLink BCM5906M Fast Ethernet"),
    ]

UNSUPPORTED_PCI_DEVICE_LIST = VMKLINUX_UNSUPPORTED_PCI_DEVICE_LIST + [
    # eg: PciInfo("8086", "1229", "Ethernet Pro 100"),
    PciInfo("0e11", "b060", "0e11:4070", "5300"),
    PciInfo("0e11", "b178", "0e11:4080", "5i"),
    PciInfo("0e11", "b178", "0e11:4082", "532"),
    PciInfo("0e11", "b178", "0e11:4083", "5312"),
    PciInfo("0e11", "0046", "0e11:4091", "6i"),
    PciInfo("0e11", "0046", "0e11:409A", "641"),
    PciInfo("0e11", "0046", "0e11:409B", "642"),
    PciInfo("0e11", "0046", "0e11:409C", "6400"),
    PciInfo("0e11", "0046", "0e11:409D", "6400 EM"),
    # Avago (LSI)
    PciInfo("1000", "005b", "0000:0000", "MegaRAID SAS Thunderbolt Controller"),
    PciInfo("1000", "0060", None       , "LSI MegaRAID SAS 1078 Controller"),
    PciInfo("1000", "006e", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2308_3 PCI-Express"),
    PciInfo("1000", "0080", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_1 PCI-Express"),
    PciInfo("1000", "0081", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_2 PCI-Express"),
    PciInfo("1000", "0082", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_3 PCI-Express"),
    PciInfo("1000", "0083", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_4 PCI-Express"),
    PciInfo("1000", "0084", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_5 PCI-Express"),
    PciInfo("1000", "0085", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2208_6 PCI-Express"),
    PciInfo("1000", "0087", "0000:0000", "Avago (LSI) Logic Fusion-MPT 6GSAS SAS2308_2 PCI-Express"),
    PciInfo("1000", "0087", "1590:0041", "HP H220 Host Bus Adapter"),
    PciInfo("1000", "0087", "1590:0043", "HP H222 Host Bus Adapter"),
    PciInfo("1000", "0087", "1590:0044", "HP H220i Host Bus Adapter"),

    PciInfo("1000", "0407", None       , "LSI MegaRAID 320-2x"),
    PciInfo("1000", "0408", None       , "LSI Logic MegaRAID"),
    PciInfo("1000", "1960", None       , "LSI Logic MegaRAID"),
    PciInfo("1000", "9010", None       , "LSI Logic MegaRAID"),
    PciInfo("1000", "9060", None       , "LSI Logic MegaRAID"),
    PciInfo("1014", "002e", None       , "SCSI RAID Adapter (ServeRAID) 4Lx"),
    PciInfo("1014", "01bd", None       , "ServeRAID Controller 6i"),
    PciInfo("103c", "3220", "103c:3225", "P600"),
    PciInfo("103c", "3230", "103c:3223", "P800"),
    PciInfo("103c", "3230", "103c:3225", "P600"),
    PciInfo("103c", "3230", "103c:3234", "P400"),
    PciInfo("103c", "3230", "103c:3235", "P400i"),
    PciInfo("103c", "3230", "103c:3237", "E500"),
    PciInfo("103c", "3238", "103c:3211", "E200i"),
    PciInfo("103c", "3238", "103c:3212", "E200"),
    PciInfo("103c", "3238", "103c:3213", "E200i"),
    PciInfo("103c", "3238", "103c:3214", "E200i"),
    PciInfo("103c", "3238", "103c:3215", "E200i"),
    PciInfo("1077", "2300", None       , "QLA2300 64-bit Fibre Channel Adapter"),
    PciInfo("1077", "2312", None       , "ISP2312-based 2Gb Fibre Channel to PCI-X HBA"),
    PciInfo("1077", "2322", None       , "ISP2322-based 2Gb Fibre Channel to PCI-X HBA"),
    PciInfo("1077", "2422", None       , "ISP2422-based 4Gb Fibre Channel to PCI-X HBA"),
    PciInfo("1077", "2432", None       , "ISP2432-based 4Gb Fibre Channel to PCI Express HBA"),
    PciInfo("1077", "4022", "0000:0000", "iSCSI device"),
    PciInfo("1077", "4022", "1077:0122", "iSCSI device"),
    PciInfo("1077", "4022", "1077:0124", "iSCSI device"),
    PciInfo("1077", "4022", "1077:0128", "iSCSI device"),
    PciInfo("1077", "4022", "1077:012e", "iSCSI device"),
    PciInfo("1077", "4032", "1077:014f", "iSCSI device"),
    PciInfo("1077", "4032", "1077:0158", "iSCSI device"),
    PciInfo("1077", "5432", None       , "SP232-based 4Gb Fibre Channel to PCI Express HBA"),
    PciInfo("1077", "6312", None       , "SP202-based 2Gb Fibre Channel to PCI-X HBA"),
    PciInfo("1077", "6322", None       , "SP212-based 2Gb Fibre Channel to PCI-X HBA"),
    PciInfo("1095", "0643", None       , "CMD643 IDE/PATA Controller"),
    PciInfo("1095", "0646", None       , "CMD646 IDE/PATA Controller"),
    PciInfo("1095", "0648", None       , "CMD648 IDE/PATA Controller"),
    PciInfo("1095", "0649", None       , "CMD649 IDE/PATA Controller"),
    PciInfo("1095", "0240", None       , "Adaptec AAR-1210SA SATA HostRAID Controller"),
    PciInfo("1095", "0680", None       , "Sil0680A - PCI to 2 Port IDE/PATA Controller"),
    PciInfo("1095", "3112", None       , "SiI 3112 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("1095", "3114", None       , "SiI 3114 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("1095", "3124", None       , "SiI 3124 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("1095", "3132", None       , "SiI 3132 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("1095", "3512", None       , "SiI 3512 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("1095", "3531", None       , "SiI 3531 [SATALink/SATARaid] Serial ATA Controller"),
    PciInfo("10df", "e100", None       , "LPev12000"),
    PciInfo("10df", "e131", None       , "LPev12002"),
    PciInfo("10df", "e180", None       , "LPev12000"),

    # Lancer CNA
    PciInfo("10df", "e220", "10df:e20c", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e20e", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e217", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e220", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e221", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e260", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e262", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e264", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e266", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e275", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e276", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "10df:e277", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "19e5:df02", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "19e5:df10", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "19e5:df14", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "19e5:df1c", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e220", "19e5:df1f", "Emulex OneConnect OCe15100 Ethernet Adapter"),
    PciInfo("10df", "e260", "10df:e20c", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e20e", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e217", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e220", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e260", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e262", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e264", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e266", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e275", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e276", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "10df:e277", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "19e5:df02", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "19e5:df10", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "19e5:df14", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "19e5:df1c", "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e260", "19e5:df1f", "Emulex OneConnect OCe15100 FCoE Adapter"),

    PciInfo("10df", "f095", None       , "LP952 Fibre Channel Adapter"),
    PciInfo("10df", "f098", None       , "LP982 Fibre Channel Adapter"),
    PciInfo("10df", "f0a1", None       , "LP101 2Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "f0a5", None       , "LP1050 2Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "f0d5", None       , "LP1150 4Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "f0e5", None       , "Fibre channel HBA"),
    PciInfo("10df", "f800", None       , "LP8000 Fibre Channel Host Adapter"),
    PciInfo("10df", "f900", None       , "LP9000 Fibre Channel Host Adapter"),
    PciInfo("10df", "f980", None       , "LP9802 Fibre Channel Adapter"),
    PciInfo("10df", "fa00", None       , "LP10000 2Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "fc00", None       , "LP10000-S 2Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "fc10", "10df:fc11", "LP11000-S 4Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "fc10", "10df:fc12", "LP11002-S 4Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "fc20", None       , "LPE11000S"),
    PciInfo("10df", "fd00", None       , "LP11000 4Gb Fibre Channel Host Adapter"),
    PciInfo("10df", "fe00", "103c:1708", "Fibre channel HBA"),
    PciInfo("10df", "fe00", "10df:fe00", "Fibre channel HBA"),
    PciInfo("10df", "fe00", "10df:fe22", "Fibre channel HBA"),
    PciInfo("10df", "fe05", None       , "Fibre channel HBA"),
    PciInfo("10df", "fe12", None       , "Cisco UCS CNA M71KR-Emulex"),
    PciInfo("101e", "1960", None       , "MegaRAID"),
    PciInfo("101e", "9010", None       , "MegaRAID 428 Ultra RAID Controller"),
    PciInfo("101e", "9060", None       , "MegaRAID 434 Ultra GT RAID Controller"),
    PciInfo("1022", "209a", None       , "AMD CS5536 IDE/PATA Controller"),
    PciInfo("1022", "7401", None       , "AMD Cobra 7401 IDE/PATA Controller"),
    PciInfo("1022", "7409", None       , "AMD Viper 7409 IDE/PATA Controller"),
    PciInfo("1022", "7411", None       , "AMD Viper 7411 IDE/PATA Controller"),
    PciInfo("1022", "7441", None       , "AMD 7441 OPUS IDE/PATA Controller"),
    PciInfo("1022", "7469", None       , "AMD 8111 IDE/PATA Controller"),
    PciInfo("1028", "000e", None       , "Dell PowerEdge Expandable RAID Controller"),
    PciInfo("1028", "000f", None       , "Dell PERC 4"),
    PciInfo("1028", "0013", None       , "Dell PERC 4E/Si/Di"),
    PciInfo("105a", "1275", None       , "PDC20275 Ultra ATA/133 IDE/PATA Controller"),
    PciInfo("105a", "3318", None       , "PDC20318 (SATA150 TX4)"),
    PciInfo("105a", "3319", None       , "PDC20319 (FastTrak S150 TX4)"),
    PciInfo("105a", "3371", None       , "PDC20371 (FastTrak S150 TX2plus)"),
    PciInfo("105a", "3373", None       , "PDC20378 (FastTrak 378/SATA 378)"),
    PciInfo("105a", "3375", None       , "PDC20375 (SATA150 TX2plus)"),
    PciInfo("105a", "3376", None       , "PDC20376 (FastTrak 376)"),
    PciInfo("105a", "3515", None       , "PDC40719 (FastTrak TX4300/TX4310)"),
    PciInfo("105a", "3519", None       , "PDC40519 (FastTrak TX4200)"),
    PciInfo("105a", "3570", None       , "PDC20771 (FastTrak TX2300)"),
    PciInfo("105a", "3571", None       , "PDC20571 (FastTrak TX2200)"),
    PciInfo("105a", "3574", None       , "PDC20579 SATAII 150 IDE Controller"),
    PciInfo("105a", "3577", None       , "PDC40779 (FastTrak TX2300)"),
    PciInfo("105a", "3d17", None       , "PDC40718 (SATA 300 TX4)"),
    PciInfo("105a", "3d18", None       , "PDC20518/PDC40518 (SATAII 150 TX4)"),
    PciInfo("105a", "3d73", None       , "PDC40775 (SATA 300 TX2plus)"),
    PciInfo("105a", "3d75", None       , "PDC20575 (SATAII150 TX2plus)"),
    PciInfo("105a", "4d68", None       , "PDC20268 Ultra ATA/100 IDE/PATA Controller"),
    PciInfo("105a", "4d69", None       , "PDC20269 (Ultra133 TX2) IDE/PATA Controller"),
    PciInfo("105a", "5275", None       , "PDC20276 Ultra ATA/133 IDE/PATA Controller"),
    PciInfo("105a", "6268", None       , "PDC20270 Ultra ATA/100 IDE/PATA Controller"),
    PciInfo("105a", "6269", None       , "PDC20271 Ultra ATA/133 IDE/PATA Controller"),
    PciInfo("105a", "6629", None       , "PDC20619 (FastTrak TX4000)"),
    PciInfo("105a", "7275", None       , "PDC20277 Ultra ATA/133 IDE/PATA Controller"),
    PciInfo("17d5", "5831", None       , "Xframe I 10 GbE Server/Storage adapter"),
    PciInfo("17d5", "5832", None       , "Xframe II 10 GbE Server/Storage adapter"),
    PciInfo("10de", "0035", None       , "nvidia NForce MCP04 IDE/PATA Controller"),
    PciInfo("10de", "0036", None       , "MCP04 Serial ATA Controller"),
    PciInfo("10de", "003e", None       , "MCP04 Serial ATA Controller"),
    PciInfo("10de", "0053", None       , "nvidia NForce CK804 IDE/PATA Controller"),
    PciInfo("10de", "0054", None       , "CK804 Serial ATA Controller"),
    PciInfo("10de", "0055", None       , "CK804 Serial ATA Controller"),
    PciInfo("10de", "0056", None       , "nvidia NForce Pro 2200 Network Controller"),
    PciInfo("10de", "0057", None       , "nvidia NForce Pro 2200 Network Controller"),
    PciInfo("10de", "0065", None       , "nvidia NForce2 IDE/PATA Controller"),
    PciInfo("10de", "0085", None       , "nvidia NForce2S IDE/PATA Controller"),
    PciInfo("10de", "008e", None       , "nForce2 Serial ATA Controller"),
    PciInfo("10de", "00d5", None       , "nvidia NForce3 IDE/PATA Controller"),
    PciInfo("10de", "00e3", None       , "CK8S Serial ATA Controller (v2.5)"),
    PciInfo("10de", "00ee", None       , "CK8S Serial ATA Controller (v2.5)"),
    PciInfo("10de", "00e5", None       , "nvidia NForce3S IDE/PATA Controller"),
    PciInfo("10de", "01bc", None       , "nvidia NForce IDE/PATA Controller"),
    PciInfo("10de", "0265", None       , "nvidia NForce MCP51 IDE/PATA Controller"),
    PciInfo("10de", "0266", None       , "MCP51 Serial ATA Controller"),
    PciInfo("10de", "0267", None       , "MCP51 Serial ATA Controller"),
    PciInfo("10de", "0268", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0269", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "036e", None       , "nvidia NForce MCP55 IDE/PATA Controller"),
    PciInfo("10de", "0372", None       , "nvidia NForce Pro 3600 Network Controller"),
    PciInfo("10de", "0373", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "037e", None       , "MCP55 SATA Controller"),
    PciInfo("10de", "037f", None       , "MCP55 SATA Controller"),
    PciInfo("10de", "03e7", None       , "MCP61 SATA Controller"),
    PciInfo("10de", "03ec", None       , "nvidia NForce MCP61 IDE/PATA Controller"),
    PciInfo("10de", "03f6", None       , "MCP61 SATA Controller"),
    PciInfo("10de", "03f7", None       , "MCP61 SATA Controller"),
    PciInfo("10de", "0448", None       , "nvidia NForce MCP65 IDE/PATA Controller"),
    PciInfo("10de", "045c", None       , "MCP65 SATA Controller"),
    PciInfo("10de", "045d", None       , "MCP65 SATA Controller"),
    PciInfo("10de", "045e", None       , "MCP65 SATA Controller"),
    PciInfo("10de", "045f", None       , "MCP65 SATA Controller"),
    PciInfo("10de", "054c", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "054d", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "054e", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "054f", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0550", None       , "MCP67 AHCI Controller"),
    PciInfo("10de", "0551", None       , "MCP67 SATA Controller"),
    PciInfo("10de", "0552", None       , "MCP67 SATA Controller"),
    PciInfo("10de", "0553", None       , "MCP67 SATA Controller"),
    PciInfo("10de", "0560", None       , "nvidia NForce MCP67 IDE/PATA Controller"),
    PciInfo("10de", "056c", None       , "nvidia NForce MCP73 IDE/PATA Controller"),
    PciInfo("10de", "0759", None       , "nvidia NForce MCP77 IDE/PATA Controller"),
    PciInfo("10de", "0760", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0761", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0762", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0763", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "07dc", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "07dd", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "07de", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "07df", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0ab0", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0ab1", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0ab2", None       , "nvidia NForce Network Controller"),
    PciInfo("10de", "0ab3", None       , "nvidia NForce Network Controller"),
    PciInfo("1103", "0004", None       , "HPT 366 (rev 06) IDE/PATA Controller"),
    PciInfo("1103", "0005", None       , "HPT 372 (rev 02) IDE/PATA Controller"),
    PciInfo("1103", "0006", None       , "HPT 302/302N (rev 02) IDE/PATA Controller"),
    PciInfo("1103", "0007", None       , "HPT 371/371N (rev 02) IDE/PATA Controller"),
    PciInfo("1103", "0009", None       , "HPT 372N IDE/PATA Controller"),
    PciInfo("1106", "5324", None       , "VX800 SATA/EIDE Controller"),
    PciInfo("1166", "0211", None       , "Serverworks OSB4 IDE/PATA Controller"),
    PciInfo("1166", "0212", None       , "Serverworks CSB5 IDE/PATA Controller"),
    PciInfo("1166", "0213", None       , "Serverworks CSB6 IDE/PATA Controller"),
    PciInfo("1166", "0214", None       , "Serverworks HT1000 IDE/PATA Controller"),
    PciInfo("1166", "0215", None       , "Serverworks HT1100 IDE/PATA Controller"),
    PciInfo("1166", "0217", None       , "Serverworks CSB6IDE2 IDE/PATA Controller"),
    PciInfo("1166", "0240", None       , "K2 SATA"),
    PciInfo("1166", "0241", None       , "RAIDCore RC4000"),
    PciInfo("1166", "0242", None       , "RAIDCore RC4000"),
    PciInfo("1166", "024a", None       , "BCM5785 [HT1000] SATA (Native SATA Mode)"),
    PciInfo("1166", "024b", None       , "BCM5785 [HT1000] SATA (PATA/IDE Mode)"),
    PciInfo("1166", "0410", None       , "BroadCom HT1100 SATA Controller (NATIVE SATA Mode)"),
    PciInfo("1166", "0411", None       , "BroadCom HT1100 SATA Controller (PATA/IDE Mode)"),

    # Broadcom NIC
    PciInfo("19a2", "0221", "0000:0000", "OneConnect 10Gb Gen2 PCIe Network Adapter"),
    PciInfo("19a2", "0700", "10df:e602", "FCoE CNA"),
    PciInfo("19a2", "0704", "10df:e630", "FCoE CNA"),
    PciInfo("19a2", "0704", "1137:006e", "FCoE CNA"),
    PciInfo("19a2", "0710", "0000:0000", "Emulex OCe11101-NX 10Gb 1-port network adapter"),
    PciInfo("19a2", "0710", "103c:177b", "HP BL8X0c i3 Dual Port FlexFabric 10Gb Embedded CNIC"),
    PciInfo("19a2", "0710", "103c:17a3", "HP Integrity_CN1100E PCIe 2-port CNA"),
    PciInfo("19a2", "0710", "103c:17a6", "HP Integrity NC552SFP 2P 10GbE Adapter"),
    PciInfo("19a2", "0710", "103c:184e", "HP 552M"),
    PciInfo("19a2", "0710", "103c:2151", "HP OCl11102-F5-HP Dual Port FlexFabric 10Gb Embedded CNIC"),
    PciInfo("19a2", "0710", "103c:3315", "(HP NC553i) Emulex OneConnect OCe11102 10GbE NIC CNA for HP ProLiant Intel G7 BladeSystems"),
    PciInfo("19a2", "0710", "103c:3340", "NC552SFP"),
    PciInfo("19a2", "0710", "103c:3341", "HP NC552m"),
    PciInfo("19a2", "0710", "103c:3342", "Emulex OneConnect OCe11102-I-HP NIC"),
    PciInfo("19a2", "0710", "103c:3343", "Emulex OneConnect OCm11102-I-HP NIC"),
    PciInfo("19a2", "0710", "103c:3344", "CN1100E (BK835A)"),
    PciInfo("19a2", "0710", "103c:3376", "554FLR-SFP+"),
    PciInfo("19a2", "0710", "103c:337b", "HP 554FLB"),
    PciInfo("19a2", "0710", "103c:337c", "HP 554M"),
    PciInfo("19a2", "0710", "103c:3391", "HP AT093A 10GbE-SFP PCIe 1p 8Gb FC and 1p 1/10GbE Adtr"),
    PciInfo("19a2", "0710", "103c:3392", "HP AT094A 10GbE-SFP PCIe 2p 8Gb FC and 2p 1/10GbE Adtr"),
    PciInfo("19a2", "0710", "1054:304d", "OCm11104-N2-HI"),
    PciInfo("19a2", "0710", "1054:304e", "OCl11102-F-HI"),
    PciInfo("19a2", "0710", "1054:3054", "OCm11104-F2-HI"),
    PciInfo("19a2", "0710", "10df:e70a", "Emulex OCl11104-F-X Virtual Fabric Adapter 2-port 10Gb and 2-port 1Gb LOM for HS-23"),
    PciInfo("19a2", "0710", "10df:e70b", "IBM Flex System 2-port 10Gb LOM Virtual Fabric Adapter (OCl11102F-X)"),
    PciInfo("19a2", "0710", "10df:e70f", "x440 (OCI11102-F5-X)"),
    PciInfo("19a2", "0710", "10df:e715", "90Y9332 Emulex 10GbE Virtual Fabric Adapter Advanced II for HS23"),
    PciInfo("19a2", "0710", "10df:e717", "IBM Flex System 2-port 10Gb LOM Virtual Fabric Adapter (OCI11102-F6-X)"),
    PciInfo("19a2", "0710", "10df:e718", "MZ510"),
    PciInfo("19a2", "0710", "10df:e719", "IBM Flex System 2-port 10Gb LOM Virtual Fabric Adapter (OCI11102-F7-X)"),
    PciInfo("19a2", "0710", "10df:e722", "OneConnect OCe11102-N"),
    PciInfo("19a2", "0710", "10df:e723", "OCe11102-NT"),
    PciInfo("19a2", "0710", "10df:e728", "Emulex 10GbE Custom Adapter for IBM System X (SBB 49Y7940)"),
    PciInfo("19a2", "0710", "10df:e729", "Emulex Dual Port 10Gb SFP+ Embedded VFA IIIr (90Y6456) (00Y7730)"),
    PciInfo("19a2", "0710", "10df:e72a", "Emulex 10GbE Virtual Fabric Adapter III for IBM System x"),
    PciInfo("19a2", "0710", "10df:e730", "Emulex 10GbE Virtual Fabric Adapter II for IBM System x"),
    PciInfo("19a2", "0710", "10df:e731", "IBM Flex System CN4054R 10Gb Virtual Fabric Adapter"),
    PciInfo("19a2", "0710", "10df:e734", "OneConnect OCe11102-EX/EM"),
    PciInfo("19a2", "0710", "10df:e735", "Emulex Virtual Fabric Adapter II for HS23 (81Y3120)"),
    PciInfo("19a2", "0710", "10df:e736", "OneConnect OCe11101-EX/EM"),
    PciInfo("19a2", "0710", "10df:e750", "Emulex 10GbE Virtual Fabric Adapter Advanced 2 - IBM BladeCenter (90Y3566)"),
    PciInfo("19a2", "0710", "10df:e780", "MZ512"),
    PciInfo("19a2", "0710", "1734:119f", "PY CNA Mezz Card 10Gb 2 Port NIC (MC-CNA112E)"),
    PciInfo("19a2", "0710", "1734:11c1", "OneConnect OCl11104-F1-F"),
    PciInfo("19a2", "0710", "1734:11c2", "OneConnect OCl11104-F2-F"),
    PciInfo("19a2", "0710", "1734:11c9", "OneConnect OCl11104-F3-F"),
    # Broadcom iSCSI
    PciInfo("19a2", "0710", "103c:3345", "613431-B21 (HP NC553m) Emulex OneConnect OCe11102 10GbE NIC CNA FlexFabric Adapter for HP ProLiant S"),
    PciInfo("19a2", "0712", "103c:3345", "613431-B21 (HP NC553m) Emulex OneConnect OCe11102 10GbE iSCSI CNA FlexFabric Adapter for HP ProLiant S"),
    PciInfo("19a2", "0712", "103c:3344", "HP CN1100E Converged Network Adapter"),
    PciInfo("19a2", "0712", "103c:3376", "554FLR-SFP+"),
    PciInfo("19a2", "0712", "103c:337c", "HP 554M"),
    PciInfo("19a2", "0712", "1054:304e", "OCl11102-F-HI"),
    PciInfo("19a2", "0712", "1054:3054", "OCm11104-F2-HI"),
    PciInfo("19a2", "0712", "10df:0742", "Emulex OneConnect OCe11102 10GbE iSCSI CNA"),
    PciInfo("19a2", "0712", "10df:e70a", "Emulex OCl11104-F-X Virtual Fabric Adapter 2-port 10Gb and 2-port 1Gb LOM for HS-23"),
    PciInfo("19a2", "0712", "10df:e718", "MZ510"),
    PciInfo("19a2", "0712", "10df:e728", "Emulex 10GbE Virtual Fabric Adapter II for IBM System x (49Y7950)"),
    PciInfo("19a2", "0712", "10df:e72a", "Emulex 10 GbE Virtual Fabric Adapter III for IBM System x"),
    PciInfo("19a2", "0712", "10df:e731", "IBM Flex System CN4054 10Gb VFA Ethernet (90Y3554)"),
    PciInfo("19a2", "0712", "10df:e735", "IBM Flex System CN4054R 10Gb Virtual Fabric Adapter"),
    PciInfo("19a2", "0712", "10df:e742", "OneConnect OCe11102-I/IM/IT/IX"),
    PciInfo("19a2", "0712", "10df:e750", "Emulex 10GbE Virtual Fabric Adapter Advanced 2 - IBM BladeCenter (90Y3566)"),
    PciInfo("19a2", "0712", "10df:e780", "MZ512"),
    PciInfo("19a2", "0712", "1734:119f", "PY CNA Mezz Card 10Gb 2 Port iSCSI (MC-CNA112E)"),
    PciInfo("19a2", "0712", "1734:11c1", "Emulex OneConnect OCl11102-LOM 2-port PCIe 10GbE Converged Network Adapter"),
    PciInfo("19a2", "0712", "1734:11c2", "Emulex OneConnect OCl11102-LOM 2-port PCIe 10GbE Converged Network Adapter"),
    PciInfo("19a2", "0712", "1734:11c9", "Emulex OneConnect OCl11102-LOM 2-port PCIe 10GbE Converged Network Adapter"),

    PciInfo("4040", "0001", None       , "10G Ethernet PCI Express"),
    PciInfo("4040", "0001", "103c:7047", "HP NC510F PCIe 10 Gigabit Server Adapter"),
    PciInfo("4040", "0002", None       , "10G Ethernet PCI Express CX"),
    PciInfo("4040", "0002", "103c:7048", "HP NC510C PCIe 10 Gigabit Server Adapter"),
    PciInfo("4040", "0004", None       , "IMEZ 10 Gigabit Ethernet"),
    PciInfo("4040", "0005", None       , "HMEZ 10 Gigabit Ethernet"),
    PciInfo("4040", "0100", None       , "1G/10G Ethernet PCI Express"),
    PciInfo("4040", "0100", "103c:171b", "HP NC522m Dual Port 10GbE Multifunction BL-c Adapter"),
    PciInfo("4040", "0100", "103c:1740", "HP NC375T PCI Express Quad Port Gigabit Server Adapter"),
    PciInfo("4040", "0100", "103c:3251", "HP NC375i 1G w/NC524SFP 10G Module"),
    PciInfo("4040", "0100", "103c:705a", "HP NC375i Integrated Quad Port Multifunction Gigabit Server Adapter"),
    PciInfo("4040", "0100", "103c:705b", "HP NC522SFP Dual Port 10GbE Server Adapter"),
    PciInfo("4040", "0100", "152d:896b", "Quanta SFP+ Dual Port 10GbE Adapter"),
    PciInfo("4040", "0100", "4040:0123", "Dual Port 10GbE CX4 Adapter"),
    PciInfo("4040", "0100", "4040:0124", "QLE3044 (NX3-4GBT) Quad Port PCIe 2.0 Gigabit Ethernet Adapter"),
    PciInfo("4040", "0100", "4040:0125", "NX3-IMEZ 10 Gigabit Ethernet"),
    PciInfo("4040", "0100", "4040:0126", "QLE3142 (NX3-20GxX) Dual Port PCIe 2.0 10GbE SFP+ Adapter"),
    # Intel NIC
    PciInfo("8086", "1001", None       , "82543GC Gigabit Ethernet Controller (Fiber)"),
    PciInfo("8086", "1004", None       , "82543GC Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "1008", None       , "82544EI Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "1009", None       , "82544EI Gigabit Ethernet Controller (Fiber)"),
    PciInfo("8086", "100c", None       , "82544GC Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "100d", None       , "82544GC Gigabit Ethernet Controller (LOM)"),
    PciInfo("8086", "100e", None       , "82540EM Gigabit Ethernet Controller"),
    PciInfo("8086", "1011", None       , "82545EM Gigabit Ethernet Controller (Fiber)"),
    PciInfo("8086", "1012", None       , "82546EM Gigabit Ethernet Controller (Fiber)"),
    PciInfo("8086", "1013", None       , "82541EI Gigabit Ethernet Controller"),
    PciInfo("8086", "1014", None       , "82541ER Gigabit Ethernet Controller"),
    PciInfo("8086", "1015", None       , "82540EM Gigabit Ethernet Controller (LOM)"),
    PciInfo("8086", "1016", None       , "82540EP Gigabit Ethernet Controller"),
    PciInfo("8086", "1017", None       , "82540EP Gigabit Ethernet Controller"),
    PciInfo("8086", "1018", None       , "82541EI Gigabit Ethernet Controller"),
    PciInfo("8086", "1019", None       , "82547EI Gigabit Ethernet Controller"),
    PciInfo("8086", "101a", None       , "82547EI Gigabit Ethernet Controller"),
    PciInfo("8086", "101d", None       , "82546EB Gigabit Ethernet Controller"),
    PciInfo("8086", "101e", None       , "82540EP Gigabit Ethernet Controller"),
    PciInfo("8086", "1026", None       , "82545GM Gigabit Ethernet Controller"),
    PciInfo("8086", "1027", None       , "82545GM Gigabit Ethernet Controller"),
    PciInfo("8086", "1028", None       , "82545GM Gigabit Ethernet Controller"),
    PciInfo("8086", "1049", "0000:0000", "82566MM Gigabit Network Connection"),
    PciInfo("8086", "104a", "0000:0000", "82566DM Gigabit Network Connection"),
    PciInfo("8086", "104b", "0000:0000", "82566DC Gigabit Network Connection"),
    PciInfo("8086", "104c", "0000:0000", "82562V 10/100 Network Connection"),
    PciInfo("8086", "104d", "0000:0000", "82566MC Gigabit Network Connection"),
    PciInfo("8086", "105e", "0000:0000", "Intel PRO/1000 PT Dual Port Network Connection"),
    PciInfo("8086", "105e", "8086:005e", "PRO/1000 PT Dual Port Server Connection"),
    PciInfo("8086", "105e", "8086:105e", "PRO/1000 PT Dual Port Network Connection"),
    PciInfo("8086", "105e", "8086:115e", "Intel PRO/1000 PT Dual Port Server Adapter"),
    PciInfo("8086", "105e", "8086:125e", "Intel PRO/1000 PT Dual Port Server Adapter"),
    PciInfo("8086", "105e", "8086:135e", "PRO/1000 PT Dual Port Server Adapter"),
    PciInfo("8086", "105f", "0000:0000", "Intel PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "105f", "8086:0000", "PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "105f", "8086:005a", "PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "105f", "8086:115f", "PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "105f", "8086:125f", "PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "105f", "8086:135f", "PRO/1000 PF Dual Port Server Adapter"),
    PciInfo("8086", "1060", "0000:0000", "Intel PRO/1000 PB Dual Port Server Connection"),
    PciInfo("8086", "1060", "8086:0060", "PRO/1000 PB Dual Port Server Connection"),
    PciInfo("8086", "1060", "8086:1060", "PRO/1000 PB Dual Port Server Connection"),
    PciInfo("8086", "1075", None       , "82547GI Gigabit Ethernet Controller"),
    PciInfo("8086", "1076", None       , "82541GI Gigabit Ethernet Controller"),
    PciInfo("8086", "1077", None       , "82541GI Gigabit Ethernet Controller"),
    PciInfo("8086", "1078", None       , "82541ER Gigabit Ethernet Controller"),
    PciInfo("8086", "1079", None       , "82546EB Gigabit Ethernet Controller"),
    PciInfo("8086", "107a", None       , "82546GB Gigabit Ethernet Controller"),
    PciInfo("8086", "107b", None       , "82546GB Gigabit Ethernet Controller"),
    PciInfo("8086", "107c", None       , "82541PI Gigabit Ethernet Controller"),
    PciInfo("8086", "107d", "0000:0000", "Intel PRO/1000 PT Network Connection"),
    PciInfo("8086", "107d", "8086:1082", "Intel PRO/1000 PT Server Adapter"),
    PciInfo("8086", "107d", "8086:1092", "PRO/1000 PT Server Adapter"),
    PciInfo("8086", "107e", "0000:0000", "Intel PRO/1000 PF Network Connection"),
    PciInfo("8086", "107e", "8086:1084", "Intel PRO/1000 PF Server Adapter"),
    PciInfo("8086", "107e", "8086:1085", "PRO/1000 PF Server Adapter"),
    PciInfo("8086", "107e", "8086:1094", "PRO/1000 PF Server Adapter"),
    PciInfo("8086", "107f", "0000:0000", "Intel PRO/1000 PB Server Connection"),
    PciInfo("8086", "108a", None       , "82546GB Gigabit Ethernet Controller"),
    PciInfo("8086", "108b", "0000:0000", "82573V Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "108c", "0000:0000", "82573E Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "1096", "0000:0000", "Intel PRO/1000 EB Network Connection with I/O Acceleration"),
    PciInfo("8086", "1098", "0000:0000", "Intel PRO/1000 EB Backplane Connection with I/O Acceleration"),
    PciInfo("8086", "1098", "1458:0000", "NIC Goshan"),
    PciInfo("8086", "1099", None       , "82546GB Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "109a", "0000:0000", "82573L Gigabit Ethernet Controller"),
    PciInfo("8086", "109a", "8086:109a", "PRO/1000 PL Network Connection"),
    PciInfo("8086", "10a4", "0000:0000", "Intel PRO/1000 PT Quad Port Server Adapter"),
    PciInfo("8086", "10a4", "8086:10a4", "PRO/1000 PT Quad Port Server Adapter"),
    PciInfo("8086", "10a4", "8086:11a4", "PRO/1000 PT Quad Port Server Adapter"),
    PciInfo("8086", "10a5", "0000:0000", "Intel PRO/1000 PF Quad Port Server Adapter"),
    PciInfo("8086", "10a5", "8086:10a5", "PRO/1000 PF Quad Port Server Adapter"),
    PciInfo("8086", "10a5", "8086:10a6", "PRO/1000 PF Quad Port Server Adapter"),
    PciInfo("8086", "10b5", None       , "82546GB Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "10b9", "0000:0000", "82572EI Gigabit Ethernet Controller (Copper)"),
    PciInfo("8086", "10b9", "8086:1083", "PRO/1000 PT Desktop Adapter"),
    PciInfo("8086", "10b9", "8086:1093", "PRO/1000 PT Desktop Adapter"),
    PciInfo("8086", "10ba", "0000:0000", "Intel PRO/1000 EB1 Network Connection with I/O Acceleration"),
    PciInfo("8086", "10bb", "0000:0000", "Intel PRO/1000 EB1 Backplane Connection with I/O Acceleration"),
    PciInfo("8086", "10bc", "0000:0000", "Intel PRO/1000 PT Quad Port LP Server Adapter"),
    PciInfo("8086", "10bc", "8086:11bc", "PRO/1000 PT Quad Port LP Server Adapter"),
    PciInfo("8086", "10bc", "8086:10bc", "PRO/1000 PT Quad Port LP Server Adapter"),
    PciInfo("8086", "10bd", "0000:0000", "82566DM-2 Gigabit Network Connection"),
    PciInfo("8086", "10bf", "0000:0000", "82567LF Gigabit Network Connection"),
    PciInfo("8086", "10c0", "0000:0000", "82562V-2 10/100 Network Connection"),
    PciInfo("8086", "10c2", "0000:0000", "82562G-2 10/100 Network Connection"),
    PciInfo("8086", "10c3", "0000:0000", "82562GT-2 10/100 Network Connection"),
    PciInfo("8086", "10c4", "0000:0000", "82562GT 10/100 Network Connection"),
    PciInfo("8086", "10c5", "0000:0000", "82562G 10/100 Network Connection"),
    PciInfo("8086", "10c7", "8086:a16f", "Intel 10 Gigabit XF SR Server Adapter"),
    PciInfo("8086", "10cb", "0000:0000", "82567V Gigabit Network Connection"),
    PciInfo("8086", "10cc", "0000:0000", "82567LM-2 Gigabit Network Connection"),
    PciInfo("8086", "10cd", "0000:0000", "82567LF-2 Gigabit Network Connection"),
    PciInfo("8086", "10ce", "0000:0000", "82567V-2 Gigabit Network Connection"),
    PciInfo("8086", "10d5", "0000:0000", "82571PT Gigabit PT Quad Port Server ExpressModule"),
    PciInfo("8086", "10d9", "0000:0000", "82571EB Dual Port Gigabit Mezzanine Adapter"),
    PciInfo("8086", "10da", "0000:0000", "82571EB Quad Port Gigabit Mezzanine Adapter"),
    PciInfo("8086", "10de", "0000:0000", "82567LM-3 Gigabit Network Connection"),
    PciInfo("8086", "10df", "0000:0000", "82567LF-3 Gigabit Network Connection"),
    PciInfo("8086", "10e5", "0000:0000", "82567LM-4 Gigabit Network Connection"),
    PciInfo("8086", "10ea", "0000:0000", "82577LM Gigabit Network Connection"),
    PciInfo("8086", "10eb", "0000:0000", "82577LC Gigabit Network Connection"),
    PciInfo("8086", "10ef", "0000:0000", "82578DM Gigabit Network Connection"),
    PciInfo("8086", "10f0", "0000:0000", "82578DC Gigabit Network Connection"),
    PciInfo("8086", "10f5", "0000:0000", "82567LM Gigabit Network Connection"),
    PciInfo("8086", "1501", "0000:0000", "82567V-3 Gigabit Network Connection"),

    PciInfo("8086", "1960", "101e:0438", "MegaRAID 438 Ultra2 LVD RAID Controller"),
    PciInfo("8086", "1960", "101e:0466", "MegaRAID 466 Express Plus RAID Controller"),
    PciInfo("8086", "1960", "101e:0467", "MegaRAID 467 Enterprise 1500 RAID Controller"),
    PciInfo("8086", "1960", "101e:09a0", "PowerEdge Expandable RAID Controller 2/SC"),
    PciInfo("8086", "1960", "1028:0467", "PowerEdge Expandable RAID Controller 2/DC"),
    PciInfo("8086", "1960", "1028:1111", "PowerEdge Expandable RAID Controller 2/SC"),
    PciInfo("8086", "1960", "103c:03a2", "MegaRAID"),
    PciInfo("8086", "1960", "103c:10c6", "MegaRAID 438, HP NetRAID-3Si"),
    PciInfo("8086", "1960", "103c:10c7", "MegaRAID T5, Integrated HP NetRAID"),
    PciInfo("8086", "1960", "103c:10cc", "MegaRAID, Integrated HP NetRAID"),
    PciInfo("8086", "294c", "0000:0000", "82566DC-2 Gigabit Network Connection"),
    PciInfo("9005", "0250", None       , "ServeRAID Controller"),
    PciInfo("9005", "0410", None       , "AIC-9410"),
    PciInfo("9005", "0411", None       , "AIC-9410"),
    PciInfo("9005", "0412", None       , "AIC-9410"),
    PciInfo("9005", "041e", None       , "AIC-9410"),
    PciInfo("9005", "041f", None       , "AIC-9410"),
    PciInfo("9005", "8000", None       , "ASC-29320A U320"),
    PciInfo("9005", "800f", None       , "AIC-7901 U320"),
    PciInfo("9005", "8010", None       , "ASC-39320 U320"),
    PciInfo("9005", "8011", None       , "39320D Ultra320 SCSI"),
    PciInfo("9005", "8011", "0e11:00ac", "ASC-32320D U320"),
    PciInfo("9005", "8011", "9005:0041", "ASC-39320D U320"),
    PciInfo("9005", "8012", None       , "ASC-29320 U320"),
    PciInfo("9005", "8013", None       , "ASC-29320B U320"),
    PciInfo("9005", "8014", None       , "ASC-29320LP U320"),
    PciInfo("9005", "8015", None       , "AHA-39320B"),
    PciInfo("9005", "8016", None       , "AHA-39320A"),
    PciInfo("9005", "801c", None       , "AHA-39320DB / AHA-39320DB-HP"),
    PciInfo("9005", "801d", None       , "AIC-7902B U320 OEM"),
    PciInfo("9005", "801e", None       , "AIC-7901A U320"),
    PciInfo("9005", "801f", None       , "AIC-7902 U320, AIC-7902 Ultra320 SCSI"),
    PciInfo("9005", "8094", None       , "ASC-29320LP U320 w/HostRAID"),
    PciInfo("9005", "809e", None       , "AIC-7901A U320 w/HostRAID"),
    PciInfo("9005", "809f", None       , "AIC-7902 U320 w/HostRAID"),
    #nmlx4_core
    PciInfo("15b3", "1007", None       , "ConnectX-3 Pro EN network interface card"),
    PciInfo("15b3", "1004", None       , "MT27500/MT27520 Family [ConnectX-3/ConnectX-3 Pro Virtual Function]"),
    PciInfo("15b3", "1003", None       , "MT27500 Family [ConnectX-3]"),
    PciInfo("15b3", "01f8", None       , "MT27520 [ConnectX-3 Pro Flash Recovery]"),
    PciInfo("15b3", "01f6", None       , "MT27500 [ConnectX-3 Flash Recovery]"),
    #brcmfcoe
    PciInfo("19a2", "0714", None       , "Emulex OneConnect OCe11100 FCoE Initiator"),
    #lpfc
    PciInfo("10df", "e260", None     , "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "e268", None     , "Emulex OneConnect OCe15100 FCoE Adapter"),
    PciInfo("10df", "f015", None     , "Emulex LPe1250 8Gb PCIe Fibre Channel Adapter"),
    PciInfo("10df", "f100", None     , "Emulex LPe12000 8Gb PCIe Fibre Channel Adapter"),
    PciInfo("10df", "f180", None     , "Emulex LPSe12002-ML1 8Gb PCIe EmulexSecure Fibre Channel Adapter"),
    PciInfo("10df", "fc40", None     , "Emulex LPe12000-S 8Gb Fibre Channel Adapter"),
    ]

# PCI classes that have native class drivers.
NATIVE_PCI_CLASS_DRIVER = [
    '010601',   # AHCI    vmw_ahci
    '010802',   # NVMe    nvme_pcie(7.0)/nvme(before-7.0)
    ]

# Software storage adapters are treated same as having native drivers
SOFTWARE_ADAPTER = [
    'iscsi_vmk',   # iSCSI Software Adapter
    'qfle3f',      # QLogic Inc. FCoE Adapter
    ]

class SystemProbeESXi(object):
    '''Initiate shared attributes, data and options for precheck.
       Attributes:
           environment    - one of WEASEL_ENV, VUM_ENV and ESXCLI_ENV,
                            affects how attributes are populated and
                            how some tests behave.
           bootDeviceName - name of the boot device.
           imageMetadata  - an ImageMetadata instance that holds image
                            information.
           nativeDevices  - device vmkernel names on the host that are
                            backed by native drivers.
    '''
    WEASEL_ENV = 'weasel'
    VUM_ENV = 'vum'
    ESXCLI_ENV = 'esxcli'

    def __init__(self, environment, freshInstall=False, keepDatastore=False,
                 bootDeviceName=None, hostBootbankPath=None,
                 hostLockerPath=None, hostImageProfile=None,
                 targetImageProfile=None):
        '''Arguments other than attributes:
           freshInstall       - when set to True, target image profile is the
                                same as the upgrade-to (e.g. ISO) image
                                profile.
           keepDatastore      - set to True when preserving VMFS in weasel.
           hostBootbankPath   - host's last booted bootbank, for use of loading
                                old VIBs in weasel. Useful only for ISO
                                upgrade.
           hostLockerPath     - host's locker path, for use of loading old VIBs
                                in weasel. Useful only for ISO upgrade.
           hostImageProfile   - the image profile on the host; passed in by
                                Image Manager during a scan.
           targetImageProfile - the final target image profile that the host
                                will boot; esxcli passes it in for VmkLinux
                                checks, and Image Manager passes it in for scan.
        '''
        self.environment = environment
        self.bootDeviceName = bootDeviceName

        # If the current ESXi enviroment is native driver only.
        self.isNativeDriverEnv = not os.path.exists(
                                        os.path.join(os.path.sep,
                                                     VMKLINUX_MOD_PATH))

        if environment != self.ESXCLI_ENV:
            self.imageMetadata = ImageMetadata(environment, freshInstall,
                                               hostBootbankPath, hostLockerPath)
            # Identify devices that will be backed by native drivers post
            # upgrade.
            self.nativeDevices = self._getNativeDevices()
        elif targetImageProfile:
            # VmkLinux check mode for esxcli, or Image Manager scan.
            # No image profile check mode in esxcli requires no image metadata,
            # the mode is for backward compatibility where VmkLinux checks
            # are conducted separately.
            self.imageMetadata = ImageMetadata(environment,
                                          hostImageProfile=hostImageProfile,
                                          targetImageProfile=targetImageProfile)
            self.nativeDevices = self._getNativeDevices()

        self.bootBankSize = self._getBootBankSize(keepDatastore)

    @property
    def isNativeDriverTarget(self):
        """Returns if the target image supports only native drivers.
        """
        return self.imageMetadata.isNativeTargetImage

    vumEnvironment = property(lambda self: self.environment == self.VUM_ENV)
    upgradeImageProfile = property(lambda self:
                                      self.imageMetadata.upgradeImageProfile)
    targetImageProfile = property(lambda self:
                                      self.imageMetadata.targetImageProfile)

    def _getNativeDevices(self):
        """Find all devices which are supported by the native drivers provided
           by the final target image profile.

           First, read out the PCIID tags from the driver VIBs.
           Note that only native drivers built with a NativeDDK from the 6.5
           release or later exhibit PCIID tags in this fashion.

           Then scan the output of 'localcli hardware pci list' to determine
           which of the PCI devices present on this system are directly
           supported by the native drivers by matching PCIID tags.
           There are catch-all native drivers that handle entire PCI classes,
           not particular PCI IDs. PCI devices that fall into these classes
           will be marked as native.

           There are additional storage devices with adapter names
           such as vmhba32, vmhba33, which don't correspond to
           PCI aliases - and thus won't shop up in the pci list.
           For these, we will scan the output of 'localcli storage core
           adapter list'.

           These devices are are supported if one of these two
           criteria are met:
           => If the driver's uid begins with "uid."
           => If the base PCI device has a vmhba<N> alias and
              it is supported by a native driver.
           Case 1 is used to pick up vmkusb devices.
           Case 2 is used to pick up supported vmk_ahci and vmkata devices.

           This algorithm excludes the CNA cases supported by vmklinux drivers
           such as "bnx2i", "bnx2fc" and "fcoe" - since the base device will
           be a NIC.
        """
        if self.isNativeDriverEnv:
            # If the current (before upgrade) environment is already native
            # driver only, there is no need to continue.
            return set()

        nativeDevices = set()
        pciDriverTags = []
        pciTagRegex = re.compile(r"PCIID\s+(?P<id>[0-9a-z.]*)\s*\Z")
        for vib in self.targetImageProfile.vibs.values():
            if hasattr(vib, 'swtags'):
                for tag in vib.swtags:
                    m = pciTagRegex.match(tag)
                    if m:
                        pciDriverTags.append(m.group('id'))

        # Now find which of the vmhba(s) and vmnic(s) which will have
        # native drivers.  We record the devices by their sbdfAddress
        # because we will need to match that up with the output from
        # 'localcli storage core adapter list'.
        #
        # All of the sbdf address(es) emitted by esxcli are in lower case
        # hex, so that base or case conversion is not required.
        deviceNames = re.compile(r"(vmhba|vmnic)(0|([1-9][0-9]*))\Z")
        cmd = 'hardware pci list'
        pciDevList = []
        try:
            pciDevList = runLocalcli(cmd)
        except Exception as e:
            log.error('Failed to obtain PCI info: %s' % str(e))

        # Identify the mapping (sbdf -> device) for known native
        # driver supported devices.  This only find the sbdf addresses
        # for the HBAs.
        nativeSbdfIndex = {}
        for device in pciDevList:
            name = device['VMkernel Name']
            if deviceNames.match(name):
                sbdfAddress = device['Address']
                vendId = device['Vendor ID']
                devId = device['Device ID']
                subVendId = device['SubVendor ID']
                subDevId = device['SubDevice ID']
                pciClass = device['Device Class']
                pgmIf = device['Programming Interface']
                classCode = '%04x%02x' % (pciClass, pgmIf)

                # Inside this condition, we also add the sbdf address to the
                # native sbdf index map. This is done because native PCI
                # class drivers generate soft adapter names, sdbf address
                # helps identify them.
                if classCode in NATIVE_PCI_CLASS_DRIVER:
                    log.debug('%s: identified native driver for '
                              'device' % name)
                    nativeDevices.add(name)
                    log.debug('%s: added to native sdbf index as pci class '
                              'driver' % sbdfAddress)
                    nativeSbdfIndex[sbdfAddress] = name
                    continue

                hwId = ('%04x%04x%04x%04x%s'
                        % (vendId, devId, subVendId, subDevId,
                           classCode))

                # Note that class drivers have the '.' characters at the
                # beginning or in the middle of the device specification
                # (driverTag).  Use re's match function to evaluate
                # the '.' characters as wildcards.
                for driverTag in pciDriverTags:
                    if re.match(driverTag, hwId):
                        log.debug('%s: identified native driver for '
                                  'device' % name)
                        nativeDevices.add(name)

        # Now find additional devices (i.e. usb, sata, fcoe and iscsi)
        # that have native drivers, but cannot be matched by PCIID.  We
        # find them by the sbdfAddress by scraping the description
        # field in the output from 'esxcli storage core adapter list'
        #
        # PR 2306705: we have to run this command by calling localcli
        # directly, rather than using esxclipy, to be able to load 32-bit
        # plugins.
        #
        # Admittedly, this method is a bit fragile.  Moreover, the
        # sbdf address changed from decimal in 5.5ga to hex later on.
        # We tolerate both forms by using string comparison within the
        # single command 'localcli storage core adapter list'.
        #
        sbdfRegex = re.compile(r"\((?P<sbdf>[0-9A-Fa-f:.]+)\)")
        usbRegex = re.compile(r"usb\.")
        cmd = 'localcli --formatter=json storage core adapter list'
        adapterList = []
        try:
            out = run(cmd)
            adapterList = json.loads(out.decode())
        except Exception as e:
            log.error("Failed to obtain adapter info: %s" % str(e))

        if adapterList:
            for adapter in adapterList:
                name = adapter['HBA Name']
                description = adapter['Description']
                m = sbdfRegex.match(description)
                if m:
                    sbdfAddress = m.group('sbdf')
                    if name in nativeDevices:
                        nativeSbdfIndex[sbdfAddress] = name
                        log.debug("%s: identified sbdf '%s' for a native "
                                  "supported device using description '%s'"
                                  % (name, sbdfAddress, description))

            # Now look for native supported devices in the localcli
            # output.
            # The below loop finds and cache sdbf addresses that map
            # to native adapters.
            for adapter in adapterList:
                name = adapter['HBA Name']
                uid = adapter['UID']
                description = adapter['Description']
                driver = adapter['Driver']

                # case 1: To find usb devices (we assume all are supported
                #         by native).
                if usbRegex.match(uid):
                    log.debug("%s: found usb device with uid '%s' - "
                              "assuming native support" % (name, uid))
                    nativeDevices.add(name)
                    continue

                # case 2: To mark the software storage adapters same as having
                #         native drivers
                if driver in SOFTWARE_ADAPTER:
                    log.debug('%s: identified native device as it is on'
                              ' software adapter %s' % (name, driver))
                    nativeDevices.add(name)
                    continue

                # case 3: Find vmkata/vmk_ahci devices supported by native.
                #         We assume that if the base PCI device is supported
                #         by a native driver then the others are as well.
                if name not in nativeDevices:
                    m = sbdfRegex.match(description)
                    if m:
                        sbdfAddress = m.group('sbdf')
                        if sbdfAddress in nativeSbdfIndex.keys():
                            baseName = nativeSbdfIndex[sbdfAddress]
                            log.debug("%s: found base native driver '%s' for "
                                      "non-pciiid device with sbdfAddress '%s'"
                                      % (name, baseName, sbdfAddress))
                            nativeDevices.add(name)
                        else:
                            log.debug("%s: rejected for native driver support "
                                      "non-pciiid device with sbdfAddress '%s' "
                                      "and description '%s'" %
                                      (name, sbdfAddress, description))
        log.debug('Found native devices on the host: %s' % str(nativeDevices))
        return nativeDevices

    def _getBootBankSize(self, keepDatastore):
        """Returns the size of the bootbank in MiB.
        """
        if self.environment == self.WEASEL_ENV:
            # Compute based on disk name and keepDatastore option.
            from systemStorage.autoPartition import computeBootbankSize
            from systemStorage.esxdisk import EsxDisk
            disk = EsxDisk(self.bootDeviceName)
            disk.scanPartitions()
            return computeBootbankSize(disk, keepDatastore)
        else:
            return BootBankInstaller.BootBankInstaller.GetStageBootBankSize()

    def isDeviceNativePostUpgrade(self, deviceName):
        '''Checks if a device will be backed by a native driver post upgrade.
        '''
        return self.isNativeDriverEnv or deviceName in self.nativeDevices

class ImageMetadata(object):
    '''Image metadata related to the install/upgrade action.
    '''
    def __init__(self, environment, freshInstall=False, hostBootbankPath=None,
                 hostLockerPath=None, hostImageProfile=None,
                 targetImageProfile=None):
        if environment == SystemProbeESXi.ESXCLI_ENV:
            # esxcli VmkLinux mode or Image Manager scan, take image profile
            # input only.
            if targetImageProfile:
                self.targetImageProfile = targetImageProfile
            if hostImageProfile:
                self.upgradeImageProfile = hostImageProfile
        else:
            self.upgradeImageProfile = self._getUpgradeImageProfile(environment)
            if freshInstall:
                # In ISO fresh install, target is the upgade-to image.
                self.targetImageProfile = self.upgradeImageProfile
            else:
                hostImageProfile = self._getHostImageProfile(environment,
                                                             hostBootbankPath,
                                                             hostLockerPath)
                self.targetImageProfile = self._getTargetImageProfile(
                                                      hostImageProfile,
                                                      self.upgradeImageProfile)
            if environment == SystemProbeESXi.VUM_ENV:
                # Size for ISO copying in VUM.
                self.sizeOfUpgradeImage = self._calcImageSize(
                                                       self.upgradeImageProfile)
        self.isNativeTargetImage = self._isNativeImage(self.targetImageProfile)

    @staticmethod
    def _getVisorfsDatabase():
        '''Loads and returns the visorFS database.
        '''
        dbPath = os.path.join('/', InstallerCommon.LiveImage.DB_DIR)
        d = Database.Database(dbPath, dbcreate=False)
        d.Load()
        d.profile.PopulateVibs(d.vibs)
        return d

    @staticmethod
    def _getIsoMetadata():
        '''Loads metatada.zip of the ISO and returns the metadata object.
        '''
        m = Metadata.Metadata()
        m.ReadMetadataZip(os.path.join(SCRIPT_DIR, "metadata.zip"))

        if len(m.profiles) != 1:
            raise Exception("Multiple or no image profiles in metadata!")

        p = list(m.profiles.values())[0]
        p.PopulateVibs(m.vibs)
        p.PopulateComponents(bulletins=m.bulletins)
        if p.addonID is not None:
            p.PopulateAddon(m.addons)
        if p.baseimageID is not None:
            p.PopulateBaseImage(m.baseimages)
        allComps = Bulletin.ComponentCollection(m.bulletins,
                                                ignoreNonComponents=True)
        try:
            p.PopulateReservedMetadata(allComps, m.vibs)
        except Errors.MissingComponentError as e:
            # ISO created with older tooling (EPK/PowerCLI/ImageBuilder) may
            # lack reserved component and VIB metadata. Allow the ISO to be
            # used by ignoring missing component error which would show up
            # first.
            log.warning("Missing reserved metadata: %s, the ISO might have "
                        "been generated by an old image building tool" % e.msg)
        return m

    @staticmethod
    def _getHostImageProfile(environment, hostBootbankPath, hostLockerPath):
        '''Get the image profile of the running host for VUM/ISO.
        '''
        if environment == SystemProbeESXi.WEASEL_ENV:
            # For weasel, load database with bootbank and locker paths
            from weasel import cache
            dbPath = os.path.join(hostBootbankPath, cache.ESXIMG_DBTAR_NAME)
            bootDb = Database.TarDatabase(dbPath, dbcreate=False)
            bootDb.Load()
            bootDb.profile.vibs = bootDb.vibs
            dbPath = os.path.join(hostLockerPath,
                                  cache.ESXIMG_LOCKER_PACKAGES_DIR,
                                  cache.ESXIMG_LOCKER_DB_DIR)
            lockerDb = Database.Database(dbPath, dbcreate=False)
            bootDb.profile.AddVibs(lockerDb.vibs)
            return bootDb.profile
        else:
            # isoMetadata class needs to load visorfs for weasel, here for
            # VUM environment we can use its code.
            db = ImageMetadata._getVisorfsDatabase()
            return db.profile

    @staticmethod
    def _getUpgradeImageProfile(environment):
        '''Get upgrade-to image profile for VUM/ISO.
        '''
        if environment == SystemProbeESXi.VUM_ENV:
            m = ImageMetadata._getIsoMetadata()
            return list(m.profiles.values())[0]
        else:
            d = ImageMetadata._getVisorfsDatabase()
            return d.profile

    @staticmethod
    def _getTargetImageProfile(hostImageProfile, upgradeImageProfile):
        '''Get the image profile of the host after upgrade.
        '''
        # Start from host image profile and add new/updated VIBs from ISO
        imageProfile = hostImageProfile.Copy()
        (up, _, new, _) = hostImageProfile.ScanVibs(upgradeImageProfile.vibs)
        for vid in (up | new):
            imageProfile.AddVib(upgradeImageProfile.vibs[vid], replace=True)
        imageProfile.PopulatePlatformInfo()
        return imageProfile

    @staticmethod
    def _calcImageSize(imageProfile):
        # The Metadata instance doesn't have any statistics about the size of
        # the image so we need to interate over all of the payloads to properly
        # calculate.
        totalSize = 0
        for vib in imageProfile.vibs.values():
            for payload in vib.payloads:
                totalSize += payload.size
                if payload.payloadtype == payload.TYPE_BOOT:
                    # Boot payloads are packaged a second time in imgpayld.tgz.
                    totalSize += payload.size
                elif payload.payloadtype in payload.NON_GZIP_TYPES:
                    # Misc esx-base payloads are tar'ed together again in
                    # basemisc.tgz and take about 1/5 of original size.
                    # Add 1/2 the size fo a safer count.
                    totalSize += payload.size // 2

        if imageProfile.reservedVibs:
            for vib in imageProfile.reservedVibs.values():
                # Reserved VIBs are packaged into resvibs.tgz in the ISO.
                # Use the VIB sizes for ramdisk estimation.
                totalSize += vib.packedsize
        else:
            # Reserving 20MB for an ISO generated by old tooling
            # (EPK/PowerCLI/ImageBuilder) where normally a few VIBs might have
            # been removed/replaced.
            totalSize += 20 * SIZE_MiB

        # As part of unified build, ESXio offline depot is also packaged in the
        # ISO. This is not required for upgrades of ESXi hosts via VUM but it
        # is needed for host-seeding purposes later. Its size must be
        # considerred for ramdisk sizing.
        # TODO: Make the depot size dynamic once the metadata in the ISO has
        # info about the ESXio payloads.
        totalSize += 200 * SIZE_MiB

        # The total space for the ISO is estimated at the total payload size
        # plus a 10MB fudge factor for additional bits that are not accounted
        # for in payloads, such as imgdb.tgz/cfg files, and leave some space
        # for extracting small bootloader files from basemisc.tgz.
        return totalSize + (10 * SIZE_MiB)

    @staticmethod
    def _isNativeImage(imageProfile):
        '''Return if the image profile is native driver only, which means
           no VmkLinux support.
        '''
        for v in imageProfile.vibs.values():
            if VMKLINUX_MOD_PATH in v.filelist:
                return True
        return False


# -----------------------------------------------------------------------------
def run(cmd, raiseException=True):
    log.info('Running command %s' % cmd)
    try:
        rc, output = runcommand(cmd)
    except RunCommandError as e:
        msg = "%s failed to execute: %s" % (cmd, str(e))
        if raiseException:
           raise Exception (msg)
        else:
           log.warning(msg)
    if rc != 0:
        msg = 'Command %s exited with code %d' % (cmd, rc)
        if raiseException:
           raise Exception(msg)
        else:
           log.warning(msg)
    return output

def runLocalcli(command, raiseException=True):
    '''Execute localcli command and return parsed output.
    '''
    log.info('Running command localcli %s' % command)
    localcliExecutor = esxclipy.EsxcliPy()
    rc, out = localcliExecutor.Execute(command.split())
    if rc != 0:
        msg = 'localcli call exited with status %d' % rc
        log.error('%s, output: %s' % (msg, out))
        if raiseException:
            raise Exception(msg)
        else:
            return None

    try:
        return eval(out)
    except (SyntaxError, ValueError) as e:
        msg = 'Failed to parse localcli output: %s' % str(e)
        log.error(msg)
        if raiseException:
            raise Exception(msg)
        else:
            return None

def formatValue(B=None, KiB=None, MiB=None):
    '''Takes an int value defined by one of the keyword args and returns a
    nicely formatted string like "2.6 GiB".  Defaults to taking in bytes.
    >>> formatValue(B=1048576)
    '1.00 MiB'
    >>> formatValue(MiB=1048576)
    '1.00 TiB'
    '''
    SIZE_KiB = (1024.0)
    SIZE_MiB = (SIZE_KiB * 1024)
    SIZE_GiB = (SIZE_MiB * 1024)
    SIZE_TiB = (SIZE_GiB * 1024)

    assert len([x for x in [KiB, MiB, B] if x != None]) == 1

    # Convert to bytes ..
    if KiB:
        value = KiB * SIZE_KiB
    elif MiB:
        value = MiB * SIZE_MiB
    else:
        value = B

    if value >= SIZE_TiB:
        return "%.2f TiB" % (value / SIZE_TiB)
    elif value >= SIZE_GiB:
        return "%.2f GiB" % (value / SIZE_GiB)
    elif value >= SIZE_MiB:
        return "%.2f MiB" % (value / SIZE_MiB)
    else:
        return "%s bytes" % (value)


# See http://kb.vmware.com/kb/1011712 for explanation
HV_ENABLED       = 3

def _getCpuExtendedFeatureBits():
    try:
        regs = runLocalcli('hardware cpu cpuid get --cpu=0')
    except Exception as e:
        log.error('Failed to get CPU ID: %s' % str(e))
    else:
        for reg in regs:
            if reg['Level'] == 0x80000001:
                return (reg['ECX'], reg['EDX'])
    return (0, 0)


EDX_LONGMODE_MASK = 0x20000000
ECX_LAHF64_MASK   = 0x00000001

def _parseLAHFSAHF64bitFeatures():
    # Get the extended feature bits.
    id81ECXValue, id81EDXValue = _getCpuExtendedFeatureBits()

    lahf64 = id81ECXValue & ECX_LAHF64_MASK
    longmode = id81EDXValue & EDX_LONGMODE_MASK

    amd = False
    k8ext = False

    cpu = vmkctl.CpuInfoImpl().GetCpus()[0]
    if hasattr(cpu, 'get'):
       cpu = cpu.get()
    vendor = cpu.GetVendorName()

    if vendor == 'AuthenticAMD':
        amd = True
        famValue = cpu.GetFamily()
        modValue = cpu.GetModel()

        # family == 15 and extended family == 0
        # extended model is 4-bit left shifted and added to model, must not be 0
        k8ext = (famValue == 0xF and ((modValue & 0xF0) > 0))

    # This should probably have deMorgan's applied to it...
    retval = not(not longmode or \
                 (not lahf64 and not (amd and k8ext)))
    return int(retval)

# NX-bit is bit-20 of EDX.
EDX_NX_MASK = 0x00100000

def _parseNXbitCpuFeature():
    # Get the extended features bits.
    _, id81EDXValue = _getCpuExtendedFeatureBits()
    nx_set = bool(id81EDXValue & EDX_NX_MASK)
    return int(nx_set)

def _getProductInfo():
    '''Get product and 3-digit version tuple.
    '''
    import pyvsilib
    VERSION_VSI_NODE = '/system/version'
    verInfo = pyvsilib.get(VERSION_VSI_NODE)
    # productVersion is a string in x.x.x format, convert to an int tuple.
    version = [int(part) for part in verInfo['productVersion'].split('.')]
    return verInfo['product'], version

def _parsePciInfo():
    '''Return a list of PciInfo objects detailing PCI devices on the host.
    '''
    retval = []
    pciDevices = vmkctl.PciInfoImpl().GetAllPciDevices()
    for dev in pciDevices:
        if hasattr(dev, 'get'):
            dev = dev.get()
        vendor = '{0:04x}'.format(dev.GetVendorId())
        device = '{0:04x}'.format(dev.GetDeviceId())
        subven = '{0:04x}'.format(dev.GetSubVendorId())
        subdev = '{0:04x}'.format(dev.GetSubDeviceId())
        descrp = dev.GetDeviceClassName()
        retval.append(PciInfo(vendor, device, subven + ':' + subdev, descrp))
    return retval

def allocateRamDisk(dirname, sizeInBytes):
    if os.path.exists(dirname):
        deallocateRamDisk(dirname)

    os.makedirs(dirname)
    resGroupName = 'upgradescratch'
    sizeInMegs = sizeInBytes // SIZE_MiB
    sizeInMegs += 1 # in case it got rounded down by the previous division

    cmd = 'system visorfs ramdisk add' + \
          ' -M %s' % sizeInMegs + \
          ' -m %s' % sizeInMegs + \
          ' -n %s' % resGroupName + \
          ' -t %s' % dirname + ' -p 01777'

    try:
        runLocalcli(cmd)
    except Exception as e:
        deallocateRamDisk(dirname)
        log.error('Creating ramdisk %s failed: %s' % (dirname, str(e)))
        return False
    return True

def deallocateRamDisk(dirname):
    if not os.path.exists(dirname):
        return # already removed

    cmd = 'system visorfs ramdisk remove -t %s' % dirname
    runLocalcli(cmd, raiseException=False)
    shutil.rmtree(dirname, ignore_errors=True)

#------------------------------------------------------------------------------
def memorySizeComparator(found, expected):
    '''Custom memory size comparator
    Let minimum memory go as much as 3.125% below MEM_MIN_SIZE.
    See PR 1229416 for more details.
    '''
    return operator.ge(found[0], expected[0] - (0.03125 * expected[0]))

def checkMemorySize():
    '''Check that there is enough memory
    '''
    mem = vmkctl.HardwareInfoImpl().GetMemoryInfo()
    if hasattr(mem, 'get'):
       mem = mem.get()
    found = mem.GetPhysicalMemory()

    MEM_MIN_SIZE = (4 * 1024) * SIZE_MiB
    return Result("MEMORY_SIZE", [found], [MEM_MIN_SIZE],
                  comparator=memorySizeComparator,
                  errorMsg="The memory is less than recommended",
                  mismatchCode = Result.ERROR)

#------------------------------------------------------------------------------
def upgradePathComparator(newVersion, installedVersion):
    '''Compartor used by checkUpgradePath method to check if we can upgrade.
    '''
    # Unknown installed version.
    if not installedVersion:
        return False

    # Don't allow downgrades.
    if newVersion < installedVersion:
        return False

    # Don't allow upgrades from 6.5 or prior version.
    if installedVersion < [6, 7,]:
        return False

    return True


def checkUpgradePath():
    '''Check that the upgrade from the installed version to new version
    is allowed.
    '''
    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        from weasel import devices
        from weasel.consts import PRODUCT_VERSION_NUMBER
        device = devices.getEsxDisk()
        deviceVer = list(devices.getDiskEsxVersion(device))
        deviceVerStr = '.'.join(map(str, deviceVer))
    else:
        # For esxcli usage, weasel library is loaded in a temp location,
        # use relative import to get target version.
        from ..consts import PRODUCT_VERSION_NUMBER
        deviceVer = _getProductInfo()[1]
        deviceVerStr = '.'.join(map(str, deviceVer))

    isoVer = list(map(int, PRODUCT_VERSION_NUMBER))
    isoVerStr = '.'.join(PRODUCT_VERSION_NUMBER)

    return Result("UPGRADE_PATH", isoVer, deviceVer,
                  comparator=upgradePathComparator,
                  errorMsg="Upgrading from %s to %s is not supported." %
                           (deviceVerStr, isoVerStr),
                  mismatchCode=Result.ERROR)

#-----------------------------------------------------------------------------
def checkBiosFirmwareType():
    '''Check that system has UEFI or else return a warning
    '''
    if not HostInfo.IsFirmwareUefi():
        errorMsg = ('Legacy boot detected. ESXi servers running legacy '
                    'BIOS are encouraged to move to UEFI. '
                    'Please refer to KB 84233 for more details.')
        return Result("BIOS_FIRMWARE_TYPE", [False], [True],
                    errorMsg=errorMsg,
                    mismatchCode=Result.WARNING)
    else:
        return Result("BIOS_FIRMWARE_TYPE", [True], [True])

#-----------------------------------------------------------------------------
def runDosfsck(devPath):
    """Runs dosfsck check on the given device.
    """
    from re import search

    # ESXi has no notion of the dirty bit. If the dirty bit is set, this
    # indicates that the file system was mounted by another OS, and wasn't
    # cleanly unmounted.
    DIRTY_BIT_STR = b"Dirty bit is set."

    # List of all other vFAT corruptions we care and should lead to a failure,
    # even if the dirty bit is set. If dosfsck reports any error from this list,
    # it is considered fatal and is flagged as an error during upgrade.
    FAILURE_STRS = (
        b"Bad FAT entry size: [\d]* bits.",
        b"Bad short file name ([\w]*).",
        b"Bad start cluster 1. Truncating file.",
        b"Both FATs appear to be corrupt. Giving up.",
        b"Broke cycle at cluster [\d]* in free chain.",
        b"Can't undelete directories.",
        b"Cannot change lowercase characters to uppercase.",
        b"Circular cluster chain. Truncating to",
        b"Cluster [\d]* is unreadable.",
        b"Cluster [\d]* out of range",
        b"Contains a [\w]* cluster ([\d]*). Assuming EOF.",
        b"Directory has non-zero size. Fixing it.",
        b"Duplicate directory entry.",
        b"Expected a valid '[\w]*' entry in",
        b"FATs differ and both appear to be corrupt.",
        b"FATs differ, please run fsck.fat",
        b"File size is [\d]* bytes, cluster chain length is [\d]* bytes.",
        b"First FAT appears to be corrupt and second FAT does not exist.",
        b"Free cluster summary wrong ",
        b"Has a large number of bad entries.",
        b"Internal error: cluster out of range in get_fat()",
        b"Internal error: cluster out of range in set_fat()",
        b"Internal error: Cluster chain is larger than 2^32",
        b"Internal error: didn't find cluster [\d]* in chain starting at [\d]*",
        b"Internal error: new cluster out of range in set_fat()",
        b"Internal error: next_cluster on bad cluster",
        b"Invalid '[\w]*' entry in the [\w]* slot. Fixing.",
        b"Label [\w]* stored in boot sector is not valid.",
        b"Label [\w]* stored in boot sector contains lowercase characters.",
        b"Path name too long",
        b"Reading FAT table greater than 2 is not implemented yet.",
        b"Reclaimed [\d]* unused cluster[s]? ([\d]* bytes).",
        b"Requested FAT table [\d]* does not exist.",
        b"Start cluster beyond limit ([\d]* > [\d]*). Truncating file.",
        b"Start does point to containing directory",
        b"Start does point to root directory. Deleting dir.",
        b"Truncate [\w]* to [\d]* bytes (clusters [\d]*)",
        b"Truncating [\w]* to [\d]* bytes ([\d]* clusters) because second " +
            b"is FAT32 root dir.",
        b"Volume label [\w]* stored in root directory is not valid",
        b"Volume label [\w]* stored in root directory contains lowercase " +
            b"characters."
    )

    cmd = ["/bin/dosfsck", "-V", "-n", devPath]
    rc, out = runcommand(cmd, timeout=10)
    if DIRTY_BIT_STR in out and not any(search(s, out) for s in FAILURE_STRS):
        log.warning("Ignoring 'Dirty Bit set' error as ESXi has no notion of "
                    "dirty bit.")
        return 0, out
    return rc, out

def validateVFATPartitions():
    """Runs dosfsck check on bootbanks
    """
    devPaths = []
    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        # Constructing the path using device name since the bootbank symlinks
        # are not available in weasel environment.
        if systemProbe.bootDeviceName:
            diskPath = os.path.join(os.path.sep, 'dev', 'disks',
                                    systemProbe.bootDeviceName)
            devPaths.append(diskPath + ':5')
            devPaths.append(diskPath + ':6')
        else:
            log.warn('Boot device is not found, skip dosfsck check.')
    else:
        from vmware import vsi
        bootbankLink = os.path.join(os.path.sep, 'bootbank')
        altbootbankLink = os.path.join(os.path.sep, 'altbootbank')
        bbRealPath = os.path.realpath(bootbankLink)
        altbbRealPath = os.path.realpath(altbootbankLink)
        bootbanksUUID = (os.path.basename(bbRealPath),
                         os.path.basename(altbbRealPath))

        VSI_FSVOL_PATH = "/system/fsSwitch/volumes"

        for uuid in bootbanksUUID:
            try:
                headExtent = \
                    vsi.get("%s/%s" % (VSI_FSVOL_PATH, uuid))['headExtent']
                devPaths.append(os.path.join(os.path.sep, 'dev',
                                             'disks', headExtent))
            except Exception as e:
                err = ("Failed to run dosfsck check on vFAT bootbank "
                       "partitions: %s" % str(e))
                log.exception(err)
                return Result("VFAT_CORRUPTION", [False], [True], errorMsg=err,
                              mismatchCode=Result.ERROR)

    for devPath in devPaths:
        rc, output = runDosfsck(devPath)
        log.info('dosfsck output: %s', output)
        if rc == 1:
            errorMsg = ("A problem with one or more vFAT bootbank partitions "
                        "was detected. Please refer to KB 91136 and run "
                        "dosfsck on bootbank partitions.")
            return Result("VFAT_CORRUPTION", [False], [True],
                          errorMsg=errorMsg, mismatchCode=Result.ERROR)
    return Result("VFAT_CORRUPTION", [True], [True])

#------------------------------------------------------------------------------
def checkHardwareVirtualization():
    '''Check that the system has Hardware Virtualization enabled
    '''
    hv = vmkctl.HardwareInfoImpl().GetCpuInfo()
    if hasattr(hv, 'get'):
       hv = hv.get()
    found = hv.GetHVSupport()

    return Result("HARDWARE_VIRTUALIZATION", [found], [HV_ENABLED],
                  errorMsg=("Hardware Virtualization is not a feature of"
                            " the CPU, or is not enabled in the BIOS"),
                  mismatchCode=Result.WARNING)

#------------------------------------------------------------------------------
def checkLAHFSAHF64bitFeatures():
    '''Check that the system is 64-bit with support for LAHF/SAHF in longmode
    '''

    found = _parseLAHFSAHF64bitFeatures()

    return Result("64BIT_LONGMODESTATUS", [found], [1],
                  errorMsg=("ESXi requires a 64-bit CPU with support for"
                            " LAHF/SAHF in long mode."),
                  mismatchCode=Result.ERROR)

#------------------------------------------------------------------------------
def checkNXbitCpuFeature():
    '''Check that the system has the NX bit enabled
    '''

    found = _parseNXbitCpuFeature()

    return Result("NXBIT_ENABLED", [found], [1],
                  errorMsg=("ESXi requires a CPU with NX/XD supported and"
                            " enabled."),
                  mismatchCode=Result.ERROR)

#------------------------------------------------------------------------------
def checkCpuSupported():
    '''Check if the host CPU is supported.

    For unsupported CPU models:
    Puts an error message to inform the user the CPU is not supported in this
    release and stops install/upgrade.

    For CPU models to be deprecated:
    Puts a warning message to inform the user the CPU will not be supported
    in future ESXi release and continues install/upgrade.
    '''

    cpu = vmkctl.CpuInfoImpl().GetCpus()[0]
    if hasattr(cpu, 'get'):
        cpu = cpu.get()

    vendor = cpu.GetVendorName()
    family = cpu.GetFamily()
    model = cpu.GetModel()
    stepping = cpu.GetStepping()

    allowLegacyCPU = False
    try:
        # When kernel allowLegacyCPU option is given by itself or set to TRUE,
        # installer will convert an error to a warning.
        bootCmdLine = vmkctl.SystemInfoImpl().GetBootCommandLine()
        match = re.search(r'(?i)allowLegacyCPU([^ ]*)', bootCmdLine)
        if match and match.group(1).strip('=" ').lower() in ('', 'true'):
            allowLegacyCPU = True
    except Exception:
        pass

    found = False
    errorMsg = ''
    mismatchCode = Result.SUCCESS

    CPU_ERROR = ("The CPU on this host is not supported by ESXi "
                 "8.0.3. Please refer to the VMware "
                 "Compatibility Guide (VCG) for the list of supported CPUs. "
                 "Please refer to KB 82794 for more details.")
    CPU_WARNING = ("The CPU on this host may not be supported in future "
                   "ESXi releases. Please plan accordingly. "
                   "Please refer to KB 82794 for more details.")

    CPU_OVERRIDE = ("The CPUs on this host are not supported by ESXi "
                     "8.0.3. You can override and force "
                     "install, but it is not officially supported nor "
                     "recommended. "
                     "Please refer to KB 82794 for more details.");

    if vendor == "GenuineIntel":
        # Note this logic does not check for the nuances of supported vs
        # unsupported Intel steppings within supported Intel models.
        if (family == 0x06 and
            (model in (0x4f, 0x56, 0x5e, 0x2d, 0x3c,
                       0x3e, 0x3f, 0x47) or
            (model == 0x55 and stepping == 4) or
            (model == 0x9E and stepping == 9))):
            if model in (0x4f, 0x56, 0x5e, 0x55, 0x9E):
                # Note: Warn for BDW-EP/EX (4F), BDW-DE(56), SKL-DT(5E),
                # SKL-SP/D/W (55.4), KBL-S(9E.9)
                errorMsg = CPU_WARNING
                mismatchCode = Result.WARNING
            else:
                # Note: Allow Override for SNB-EP(2D), HSW-DT(3C),
                # IVB-EP/EX(3E), HSW-EP/EX(3F), BDW-DT(47)
                errorMsg = CPU_OVERRIDE
                mismatchCode = Result.OVERRIDEWARNING
        elif family == 0x0f or (family == 0x06 and model < 0x4f):
            # Note: Family 0x0F is too old.
            # Note: Block install on family F and Block install on all
            # CPUs before BDW-EP/EX (0x4F) except above warned CPUs.
            errorMsg = CPU_ERROR
            mismatchCode = Result.ERROR
    elif vendor == "AuthenticAMD":
        # Note this logic does not check for the nuances of supported vs
        # unsupported AMD models within supported AMD Familes.
        if family ==  0x15 and model == 0x02:
            # Note: Allow Override for AMD PileDriver
            errorMsg = CPU_OVERRIDE
            mismatchCode = Result.OVERRIDEWARNING
        elif family < 0x17:
            # Note: Block everything else before Zen1 (Family 0x17)
            errorMsg = CPU_ERROR
            mismatchCode = Result.ERROR

    if systemProbe.vumEnvironment and (mismatchCode in (Result.WARNING,
       Result.OVERRIDEWARNING)):
        # VUM does not have support for warn and acknowledge, instead
        # it will fail on a warning. Log and silent the warning.
        log.info('VUM upgrade detected, silencing warning for %s CPU '
                 'family 0x%x model 0x%x.', vendor, family, model)
        found = True

    if allowLegacyCPU and mismatchCode == Result.ERROR:
        mismatchCode = Result.WARNING
        log.debug('allowLegacyCPU kernel option is set, issuing only a warning '
                  'for unsupported %s CPU with family 0x%x model 0x%x',
                  vendor, family, model)

    return Result('CPU_SUPPORT', [found], [True], errorMsg=errorMsg,
                   mismatchCode=mismatchCode)

#------------------------------------------------------------------------------
def checkCpuCores():
    '''Check that there are at least 2 cpu cores
    '''
    found = vmkctl.CpuInfoImpl().GetNumCpuCores()

    CPU_MIN_CORE = 2
    return Result("CPU_CORES", [found], [CPU_MIN_CORE],
                  comparator=operator.ge,
                  errorMsg="The host has less than %s CPU cores" % CPU_MIN_CORE,
                  mismatchCode = Result.ERROR)


#------------------------------------------------------------------------------
def checkExtraCpuLicenseRequired():
    """Check if the host requires any additional CPU license during an ISO
       upgrade from pre 7.0.
       Additional CPU license(s) is required when the total number of cores
       exceeds 32 on a single CPU:
       https://www.vmware.com/go/32-core-license-model
    """
    from weasel import devices
    from weasel.consts import VERSION_70GA
    CORES_PER_CPU_PER_LICENSE = 32

    device = devices.getEsxDisk()
    verTuple = devices.getDiskEsxVersion(device)

    required = False
    if verTuple < VERSION_70GA:
        cpuInfo = vmkctl.CpuInfoImpl()
        required = (cpuInfo.GetNumCpuCores() >
                    cpuInfo.GetNumCpuPackages() * CORES_PER_CPU_PER_LICENSE)

    return Result('EXTRA_CPU_LICENSE', [required], [False],
                  errorMsg='The host has more than %u cores per CPU, please '
                           'make sure you have purchased sufficient CPU '
                           'licenses. For more information on the change of '
                           'CPU licensing, see https://www.vmware.com/go/'
                           '32-core-license-model.' % CORES_PER_CPU_PER_LICENSE,
                  mismatchCode=Result.WARNING)


#------------------------------------------------------------------------------
def checkInitializable():
    name = 'PRECHECK_INITIALIZE'
    sanityChecks = ['version']
    passedSanityChecks = []
    try:
        _, version = _getProductInfo()
    except Exception:
        return Result(name, passedSanityChecks, sanityChecks)
    passedSanityChecks.append('version')

    sanityChecks.append('esx.conf')
    if os.path.exists(ESX_CONF_PATH):
        passedSanityChecks.append('esx.conf')

    # ... I'm sure more sanity tests will be added here ...

    return Result(name, passedSanityChecks, sanityChecks)

#------------------------------------------------------------------------------
def checkAvailableSpaceForISO():
    '''Check we booted on disk and able to initiate a ramdisk for ISO contents.
    '''
    expected = systemProbe.imageMetadata.sizeOfUpgradeImage
    if not systemProbe.bootDeviceName:
        # Won't run on PXE (no boot disk)
        return Result("SPACE_AVAIL_ISO", [0], [expected],
                      comparator=operator.ge)
    # First, we need to make sure the ISO can be copied to the ramdisk
    if allocateRamDisk(RAMDISK_NAME, expected):
        found = expected
    else:
        found = 0
    return Result("SPACE_AVAIL_ISO", [found], [expected],
                  comparator=operator.ge)

#------------------------------------------------------------------------------
def checkSaneEsxConf():
    '''Check that esx.conf is non-empty and system has a UUID.
    '''
    expected = True
    sysUuid = vmkctl.SystemInfoImpl().GetSystemUuid().uuidStr
    esxconfValid = bool(os.path.exists(ESX_CONF_PATH)
                        and os.path.getsize(ESX_CONF_PATH))
    success = esxconfValid and bool(sysUuid)
    return Result("SANE_ESX_CONF", [success], [expected])

#------------------------------------------------------------------------------
def checkVMFSVersion():
    '''Storage stack would automatically upgrade VMFS-3 to VMFS-5 with VMFS-3
       EOL (PMT 14643).
       Log an warning in VUM scan if VMFS-3 is found. ISO install/upgrade need
       not to run this check since such datastore would be upgraded at boot
       time already.
    '''
    found = False
    vmfsFs = vmkctl.StorageInfoImpl().GetVmfsFileSystems()
    for fs in vmfsFs:
        if hasattr(fs, 'get'):
            fs = fs.get()
        if fs.GetMajorVersion() == 3:
            found = True
            break
    return Result("VMFS_VERSION", [found], [False],
                  errorMsg="One or more VMFS-3 volumes have been detected."
                           " They are going to be automatically upgraded to VMFS-5.",
                  mismatchCode = Result.WARNING)

#------------------------------------------------------------------------------
def checkUnsupportedDevices():
    '''Check for any unsupported hardware via a PCI blacklist'''
    found = []

    for device in _parsePciInfo():
        if device in UNSUPPORTED_PCI_DEVICE_LIST:
            # The check before we append is a bit relaxed, so let's refine it a
            # bit.
            if not device.subsystem:
                # If the device we've probed out doesn't have a defined
                # subsystem, check if that also matches to an unsupported PCI ID
                # with an undefined subsystem.  For devices with an undefined
                # subsystem, there has to be an exact match in the unsupported
                # list.
                unsprtMatch = [ pci.subsystem for pci in
                        UNSUPPORTED_PCI_DEVICE_LIST if device == pci ]

                # Since the host's device has 'None' as its subsystem, it could
                # match anything in the unsupported list.  Make sure we find a
                # 'None' in that list.
                if None not in unsprtMatch:
                    continue

            found.append(device)

    return Result("UNSUPPORTED_DEVICES", found, [],
                  mismatchCode=Result.WARNING,
                  errorMsg="Unsupported devices are found")

def checkHostHw():
    '''Check image profile hardware platform requirement is met by the host.
    '''
    try:
        imgHws = systemProbe.targetImageProfile.GetHwPlatforms()
    except Errors.VibHwPlatformError as e:
        # Conflicting hwplatform requirements within the image profile
        log.error(str(e))
        imgHws = [Vib.HwPlatform(ImageProfile.RULE_CONFLICTING_VENDORS)]

    hostHws = []
    vendor, model = HostInfo.GetBiosVendorModel()
    hostHws.append(Vib.HwPlatform(vendor, model))
    for vendor in HostInfo.GetBiosOEMStrings():
        hostHws.append(Vib.HwPlatform(vendor, model=''))

    hwProblems = []
    for imgHw in imgHws:
        for hw in hostHws:
            prob = imgHw.MatchProblem(hw)
            if prob is None:
                # We have a match, forget any other mismatches
                hwProblems = []
                break
            hwProblems.append(prob)
        else:
            continue
        break # break out of the outer loop

    return Result("VALIDATE_HOST_HW", hwProblems, [],
                  mismatchCode=Result.ERROR,
                  errorMsg="VIBs without matching host hardware found")

def checkVibConflicts():
    ''' This check should run in weasel as well as vum-environment.
        - Validate the profile.
        - Report any conflicting Vibs.
    '''
    confvibs = []

    log.debug("Running vib conflicts check.")

    problems = systemProbe.targetImageProfile.Validate(
       noacceptance=True, noextrules=True,
       validateChecksumTypes=False)

    # Perform the vib confliction check.
    for prob in problems:
        # Profile.Validate should return a type->problem map
        # for now we'll use isinstance.
        if isinstance(prob, ImageProfile.ConflictingVIB):
            log.debug("Conflicts: %s" % str(prob))
            confvibs.append(', '.join(prob.vibids))

    rc = Result("CONFLICTING_VIBS", confvibs, [], mismatchCode=Result.ERROR,
         errorMsg="Vibs on the host are conflicting with vibs in metadata.  "
                  "Remove the conflicting vibs or use Image Builder "
                  "to create a custom ISO providing newer versions of the "
                  "conflicting vibs. ")

    if not confvibs:
        rc.code = Result.SUCCESS

    return rc

def checkVibDependencies():
    ''' This check should run in weasel as well as vum-environment.
        - Validate the profile.
        - Report any missing dependency Vibs.
    '''
    depvibs = []

    log.debug("Running vib dependency check.")

    problems = systemProbe.targetImageProfile.Validate(noacceptance=True,
                                                 noextrules=True,
                                                 validateChecksumTypes=False)

    # Perform the vib dependency check
    for prob in problems:
        # Profile.Validate should return a type->problem map
        # for now we'll use isinstance.
        if isinstance(prob, ImageProfile.MissingDependency):
            log.debug("Dependency check: %s" % str(prob))
            depvibs.append(prob.vibid)

    rc = Result("MISSING_DEPENDENCY_VIBS", depvibs, [], mismatchCode=Result.ERROR,
         errorMsg="These vibs on the host are missing dependency if continue to upgrade. "
                  "Remove these vibs before upgrade or use Image Builder  "
                  "to resolve this missing dependency issue.")

    if not depvibs:
        rc.code = Result.SUCCESS

    return rc

def checkImageProfileSize():
    ''' Calculate the installation size of the imageprofile.
        This needs to be consistent with CheckInstallationSize() in
        bora/apps/pythonroot/vmware/esximage/Installer/BootBankInstaller.py.
    '''
    totalsize = 0
    for vibid in systemProbe.targetImageProfile.vibIDs:
        vib = systemProbe.targetImageProfile.vibs[vibid]

        # Skip VIBs not applicable for the host platform.
        if not vib.hasSystemSoftwarePlatform:
            continue

        if vib.vibtype in BootBankInstaller.BootBankInstaller.SUPPORTED_VIBS:
            for payload in vib.payloads:
                if (payload.payloadtype not in
                    BootBankInstaller.BootBankInstaller.SUPPORTED_PAYLOADS):
                    continue
                # Text payloads found in basemisc.tgz on bootbank, such as
                # osl.txt, compress better than other misc payloads.
                elif payload.payloadtype == Vib.Payload.TYPE_TEXT:
                    totalsize += payload.size * 0.2
                elif (payload.payloadtype in
                      BootBankInstaller.BootBankInstaller.SUPPORTED_NONGZIP_PAYLOADS):
                    totalsize += payload.size * 0.3
                else:
                    totalsize += payload.size

    totalsizeMB = totalsize // SIZE_MiB + 1
    maximumMB = (systemProbe.bootBankSize -
                 BootBankInstaller.BootBankInstaller.BOOTBANK_PADDING_MB)
    log.info("Image size: %d MB, Maximum size: %d MB"
             % (totalsizeMB, maximumMB))
    if totalsizeMB > maximumMB:
        rc = Result("IMAGEPROFILE_SIZE", [totalsizeMB], [maximumMB],
                     mismatchCode=Result.ERROR,
                     errorMsg="The image profile size is too large" )

        log.error('The target image profile requires %d MB space, however '
                  'the maximum supported size is %d MB.' % (totalsizeMB,
                  maximumMB))
    else:
        rc = Result("IMAGEPROFILE_SIZE", [], [])
    return rc

def checkLockerSpaceAvail():
    '''Check for available space in the locker partition.
       Locker holds vmtools, but vsan stores traces here by default as well.
       An estimate approach is taken to check if there will be enough space to
       update vmtools as unpacked size is not available in metadata.
       This is only useful for VUM upgrade, since ISO upgrade would clear the
       locker partition and esximage calculates the space precisely in esxcli.
    '''
    CHECK_NAME = 'LOCKER_SPACE_AVAIL'
    CHECK_ERR = 'Locker partition does not have enough space'

    # Locker partition and the packages dir that the installer manages.
    LOCKER_PATH = os.path.join(os.path.sep, 'locker')
    LOCKER_PKG_DIR = os.path.join(LOCKER_PATH, 'packages')

    try:
        # Get free space in locker
        availSize = HostInfo.GetFsFreeSpace(LOCKER_PATH)
    except Errors.InstallationError as e:
        log.error('Failed to determine available space in locker: %s' % str(e))
        return Result(CHECK_NAME, [], [], mismatchCode=Result.ERROR,
                      errorMsg=CHECK_ERR)

    # Get current vmtools and imgdb space usage in locker
    curSize = 0
    for dirPath, _, fileNames in os.walk(LOCKER_PKG_DIR):
        for fileName in fileNames:
            filePath = os.path.join(dirPath, fileName)
            if os.path.isfile(filePath) or os.path.isdir(filePath):
               # Skip symlinks when counting size.
               curSize += os.path.getsize(filePath)

    # Get packed size of the new locker payloads
    packedSize = 0
    for vibID in systemProbe.targetImageProfile.vibIDs:
        vib = systemProbe.targetImageProfile.vibs[vibID]
        if vib.vibtype in LockerInstaller.LockerInstaller.SUPPORTED_VIBS:
            for payload in vib.payloads:
                if (payload.payloadtype in
                    LockerInstaller.LockerInstaller.SUPPORTED_PAYLOADS):
                    packedSize += payload.size

    # Estimate needed size with 85% compression rate and add a 10MB buffer
    # For a compression rate slightly worst than 85%, we get 10MB to 20MB
    # in extra of what is actually needed. The other way around, we can afford
    # a ratio around 82% given the usual packed size of locker payloads.
    neededSize = int(round(packedSize / 0.85 + 10 * SIZE_MiB, 0))

    log.info('Locker currently have %d bytes in package folder, and %d bytes '
             'free. Incoming image has %d bytes of locker payloads, estimate '
             'to take %d bytes of space.' % (curSize, availSize, packedSize,
                                             neededSize))

    # Free space should be able to handle the increase, round MiB to be
    # permissive on some hundred KiBs.
    extraNeededMiB = int(round((neededSize - curSize) / SIZE_MiB, 0))
    availMiB = int(round(availSize / SIZE_MiB, 0))
    mismatchCode = Result.SUCCESS
    if extraNeededMiB > availMiB:
        log.error('The target image profile requires about %d MiB grow space '
                  'in the locker partition, however the partition has only %d '
                  'MiB available.' % (extraNeededMiB, availMiB))
        mismatchCode = Result.ERROR

    return Result(CHECK_NAME, [availMiB], [extraNeededMiB],
                  mismatchCode = mismatchCode,
                  errorMsg=CHECK_ERR)

def checkBootDiskSize():
    """Check the boot disk is large enough for upgrade to new SystemStorage
       layout.
       This check is for VUM and esxcli cases only, as weasel checks disk size
       when selecting it.
    """
    # These imports work for VUM/esxcli because we have either set up the paths
    # with esximage.zip (in this script) or patch the patcher (from esximage
    # that imports this script).
    from systemStorage import SYSTEM_DISK_SIZE_SMALL_MB

    expected = SYSTEM_DISK_SIZE_SMALL_MB

    if systemProbe.bootDeviceName:
        diskPath = os.path.join(os.path.sep, 'dev', 'disks',
                                systemProbe.bootDeviceName)
        found = round(os.stat(diskPath).st_size / SIZE_MiB)

        mismatchCode = Result.ERROR
    else:
        # We should not be running in PXE, but don't panic.
        log.warn('Boot device is not found, skip boot disk size check')
        found = 0
        mismatchCode = Result.SUCCESS

    errMsg = ('Target version supports boot disks that are at least %u MiB in '
              'size, the boot disk has %u MiB.' % (expected, found))

    # Issue a warning only if the disk is not of USB type and its size is above
    # 4 GB but less than 8 GB
    from systemStorage import SYSTEM_DISK_MIN_HDD_SIZE_MB
    from systemStorage.esxdisk import EsxDisk
    disk = EsxDisk(systemProbe.bootDeviceName)
    if not disk.isUsb and SYSTEM_DISK_MIN_HDD_SIZE_MB > found + 1 >= expected:
        errMsg = "The boot device of the host has a capacity of %u MiB, " \
                 "Install or upgrade to future ESXi releases will not be " \
                 "supported on this boot device. Please switch to a boot " \
                 "device that is at least %u MiB in size. Refer to KB-96511 " \
                 "for further details." % \
                 (found, SYSTEM_DISK_MIN_HDD_SIZE_MB)
        # Log errors for VUM without failing, as it treats warnings as errors,
        # resulting in an incompatible scan status.
        if systemProbe.vumEnvironment:
            log.error(errMsg)
        else:
            mismatchCode = Result.WARNING
            expected = SYSTEM_DISK_MIN_HDD_SIZE_MB

    return Result('BOOT_DISK_SIZE', [found], [expected],
                  comparator=lambda fnd, exp: fnd[0] + 1 >= exp[0],
                  errorMsg=errMsg,
                  mismatchCode=mismatchCode)

def checkPackageCompliance():
    # This is used by VUM to validate that the expected VIBs have been
    # installed. Note that we only check the list of VIB IDs, not any other
    # attributes (name, acceptance level, etc.) of the image profile.

    expected = set(systemProbe.upgradeImageProfile.vibs.keys())
    newvibnames = set([vib.name for vib in
                       systemProbe.upgradeImageProfile.vibs.values()])
    issuevib = []

    try:
        bootbankdb = Database.TarDatabase("/bootbank/imgdb.tgz", False)
        bootbankdb.Load()
        try:
            lockerdb = Database.Database("/locker/packages/var/db/locker",
                                         False)
            lockerdb.Load()
            hostvibs = bootbankdb.vibs + lockerdb.vibs
        except Exception as e:
            log.error('Failed to load locker vib database: %s' % e)
            hostvibs = bootbankdb.vibs
        hostvibids = set([vib.id for vib in hostvibs.values()])
        hostvibnames = set([vib.name for vib in hostvibs.values()])

        # Log all vibs ids and unique VIBs from host and baseline
        log.info('VIBs from host: %s' % str(sorted(hostvibids)))
        log.info('VIBs from baseline: %s' % str(sorted(expected)))
        olddelta = sorted([name for name in hostvibnames if not name in
                           newvibnames])
        log.info('Unique VIBs from host: %s' % str(olddelta))
        newdelta = sorted([name for name in newvibnames if not name in
                           hostvibnames])
        log.info('Unique VIBs from baseline: %s' % str(newdelta))

        # Now scan to check versioning/replaces.
        allvibs = VibCollection.VibCollection()
        for vib in hostvibs.values():
            allvibs.AddVib(vib)
        for vib in systemProbe.upgradeImageProfile.vibs.values():
            allvibs.AddVib(vib)
        scanner = Scan.VibScanner()
        scanner.Scan(allvibs)
        # Each VIB in expected must either be on the host or be replaced by
        # something on the host.
        for vibid in expected:
            vibsr = scanner.results[vibid]
            if vibid not in hostvibids and not vibsr.replacedBy & hostvibids:
                issuevib.append(vibid)
    except Exception as e:
        msg = "Couldn't load esximage database to scan package compliance: " \
              "%s. Host may be of incorrect version." % e
        log.error(msg)
        # Scan did not succeed, make the error as an issue so the host will
        # not be marked compliant incorrectly.
        issuevib.append(msg)

    # If found >= expected is true, then everything in expected is also in
    # found. (If there are extra things in found, we are still compliant.)
    result = Result("PACKAGE_COMPLIANCE", issuevib, [],
                    mismatchCode=Result.ERROR)
    return result

def checkUpdatesPending():
    # Make sure that there are not Visor updates pending a reboot.
    expected = False
    found = False

    if os.path.exists("/altbootbank/boot.cfg"):
        f = open("/altbootbank/boot.cfg")
        for line in f:
            try:
                name, value = [word.strip() for word in line.split("=")]
                value = int(value)
                if name == "bootstate" and value == 1:
                    found = bool(int(value))
                    break
            except:
                continue
        f.close()

    return Result("UPDATE_PENDING", [found], [expected])

def checkVibChecksum():
    '''Check all the VIBs in the host image profile to see if there are any
       VIBs that have any tardisc payloads that do not have SHA 256 Gunzip
       checksum present. This will prevent VIB security verification and
       secure boot from functioning properly. If any such VIBs are present,
       we need to block the operation since this will PSOD the host
    '''

    missingchecksumvibs = []

    # Disable all other checks except for validateChecksumTypes
    problems = systemProbe.targetImageProfile.Validate(nodeps=True,
                noconflicts=True, allowobsoletes=True,
                noacceptance=True, allowfileconflicts=True,
                noextrules=True, checkCompDeps=True)

    # Perform the vib check
    missingchecksumvibs = [p.vibid for p in problems
       if isinstance(p, ImageProfile.ChecksumMissing)]

    rc = Result("MISSING_GUNZIP_CHECKSUM_VIBS", missingchecksumvibs, [],
                 mismatchCode=Result.ERROR,
                 errorMsg="These VIB(s) do not have the "
                  "required sha-256 gunzip checksum for their payloads. "
                  "This will prevent VIB security verification and "
                  "secure boot from functioning properly. Please remove "
                  "these VIBs and check with your vendor for a"
                  "replacement of these VIBs.")

    return rc

def _getVmkNicUplinkOrder(vmkNic, vsInfo):
    """Get the uplink order of the VMKernel NIC. The parameters are
       VmkNic and VirtualSwitchInfo objects returned by vmkctl.
    """
    cp = vmkNic.GetConnectionPoint().get()
    cpType = cp.GetType()
    if cpType == cp.CONN_TYPE_PG:
        # Standard switch, get the port group's uplinks.
        portGroup = vmkNic.GetPortGroup().get()
        vSwitch = portGroup.GetVirtualSwitch().get()
        return vSwitch.GetTeamingPolicy().GetUplinkOrder()
    elif cpType == cp.CONN_TYPE_DVP:
        # Distributed switch, loop and find the switch in use and get
        # its uplinks.
        dvsId = cp.GetDVPortParam().dvsId
        for dvsSwPtr in vsInfo.GetDVSwitches():
            dvsSw = dvsSwPtr.get()
            if dvsSw.GetDvsId() == dvsId:
                return dvsSw.GetUplinks()
        raise RuntimeError('Unable to find DVS with ID %s' % dvsId)
    elif cpType == cp.CONN_TYPE_OPAQUE_NET:
        # Opaque usually means it is NSX managed, no vmnic needs to be
        # returned.
        return tuple()
    else:
        # Unknown connection point
        raise RuntimeError('The VMKernel NIC has an unknown connection type')

def _getPackedIP(ipStr):
    """If ipStr is a valid IP, returns packed string representation
       of the IP. Raises socket.error otherwise.
    """
    if ':' in ipStr:
        af = socket.AF_INET6
    else:
        af = socket.AF_INET
    return socket.inet_pton(af, ipStr)

def _getUplinkOrderWithIP(ipAddress):
    """Get the uplink order of the NIC configured with the IP address.
    """
    targetPackedIP = _getPackedIP(ipAddress)
    ni = vmkctl.NetworkInfoImpl()
    for vmkNicPtr in ni.GetVmKernelNicInfo().get().GetVmKernelNics():
        vmkNic = vmkNicPtr.get()
        # Get packed IPv4 and IPv6 addresses
        ipConfig = vmkNic.GetIpConfig()
        ipv4Addr = ipConfig.GetIpv4Address().GetStringAddress()
        packedIPs = [_getPackedIP(ipv4Addr)]
        for ipv6Network in ipConfig.GetIpv6Network():
            ipv6Addr = ipv6Network.GetAddress().GetStringAddress()
            packedIPs.append(_getPackedIP(ipv6Addr))
        if targetPackedIP in packedIPs:
            # This vmkNic provides the IP, get its uplink order.
            vsInfo = ni.GetVirtualSwitchInfo().get()
            return _getVmkNicUplinkOrder(vmkNic, vsInfo)
    raise RuntimeError('Unable to find the VMkernel NIC configured with IP %s'
                       % ipAddress)

def _isNicNative(ipAddress=None):
    """Return if the NIC associated with the IP is backed by a native driver,
       or if there is at least one NIC backed with native driver (when IP is
       not given).
    """
    def _isUplinkOrderNative(upLinks):
        # With opaque networking or a standard/distributed switch
        # that is backed by a native NIC, the test passes.
        if not upLinks:
            return True
        for upLink in upLinks:
           if systemProbe.isDeviceNativePostUpgrade(upLink):
               return True
        return False

    if ipAddress:
        upLinks = _getUplinkOrderWithIP(ipAddress)
        log.info('NIC uplink order associated with ip %s: %s'
                 % (ipAddress, str(upLinks)))
        return _isUplinkOrderNative(upLinks)
    else:
        ni = vmkctl.NetworkInfoImpl()
        vsInfo = ni.GetVirtualSwitchInfo().get()
        for vmkNicPtr in ni.GetVmKernelNicInfo().get().GetVmKernelNics():
            # At least one VmkNic must pass the test.
            vmkNic = vmkNicPtr.get()
            upLinks = _getVmkNicUplinkOrder(vmkNic, vsInfo)
            log.info('NIC uplink order of VMKernel NIC %s: %s'
                     % (vmkNic.GetName(), str(upLinks)))
            if _isUplinkOrderNative(upLinks):
                return True
        return False

def checkBootNicIsNative():
    """Checks to see that a native NIC is available for the
       management traffic.
    """
    expected = True
    found = True
    if not systemProbe.isNativeDriverEnv and systemProbe.isNativeDriverTarget:
        if systemProbe.vumEnvironment:
            # Use the VC IP to figure out the management NIC.
            if not options.ip:
                log.error("Upgrading to a native only image requires "
                          "the boot ip to be passed in.")
                found = False
            else:
                try:
                    found = _isNicNative(options.ip)
                except Exception as e:
                    log.error('Failed to determine if NIC associated with IP '
                              '%s is native: %s' % (options.ip, str(e)))
                    found = False
        else:
            # esxcli case, make sure one VMKernel NIC is backed by NIC with
            # a native driver.
            try:
                found = _isNicNative()
            except Exception as e:
                log.error('Failed to determine if at least one active NIC '
                          'is native: %s' % str(e))
                found = False
    return Result("NATIVE_BOOT_NIC", [found], [expected],
             errorMsg="Boot NIC is either missing or has no "
                      "native driver available.")

def _getDiskAdapterName(device):
    """Get the adapter associated with the given disk device.
    """
    # PR 2323809: we have to run this command by calling localcli
    # directly, rather than using esxclipy, to be able to load 32-bit
    # plugins.
    cmd = 'localcli --formatter=json storage core path list -d %s' % device
    try:
        out = run(cmd)
        paths = json.loads(out.decode())
    except Exception as e:
        log.error("Failed to parse storage paths: %s." % str(e))
        return None
    else:
        if paths:
            return paths[0]['Adapter']
        else:
            log.error("Failed to determine adapter for disk %s." % device)
            return None

def checkBootbankDeviceIsNative():
    """When installing/upgrading to a native only image, the bootbank storage
       device needs to be native.
    """
    expected = True
    found = True

    if (not systemProbe.isNativeDriverEnv and systemProbe.isNativeDriverTarget
        and not HostInfo.IsPxeBooting()):
        vmhba = _getDiskAdapterName(systemProbe.bootDeviceName)
        log.info('Storage adapter for the boot disk %s: %s'
                 % (systemProbe.bootDeviceName, vmhba))
        found = systemProbe.isDeviceNativePostUpgrade(vmhba)

    return Result("NATIVE_BOOTBANK", [found], [expected],
                  errorMsg="Native drivers are missing for bootbank "
                           "storage device.")

def checkHostAcceptance():
    """Check host acceptance level with incoming imageprofile"""
    TRUST_ORDER = ImageProfile.AcceptanceChecker.TRUST_ORDER
    hostAcceptance = ""
    try:
       hostAcceptance = HostImage.HostImage().GetHostAcceptance()
    except Errors.AcceptanceGetError as e:
       pass

    if not hostAcceptance:
       return Result("HOST_ACCEPTANCE", [False], [True],
                     errorMsg="Failed to get valid host acceptance level.")
    hostAcceptanceValue = [v for k, v in TRUST_ORDER.items()
                           if k == hostAcceptance][0]
    targetAcceptance = systemProbe.upgradeImageProfile.acceptancelevel
    targetAcceptanceValue = [v for k, v in TRUST_ORDER.items()
                             if k == targetAcceptance][0]
    log.info('Host acceptance level is %s, target acceptance level is %s'
               % (hostAcceptance, targetAcceptance))
    # acceptance level cannot go down during upgrade
    if hostAcceptanceValue > targetAcceptanceValue:
        err = 'Acceptance level of the host has to change from %s to %s ' \
              'to match with the new imageprofile and proceed with ' \
              'upgrade.' % (hostAcceptance, targetAcceptance)
        log.error(err)
        return Result('HOST_ACCEPTANCE', [False], [True], errorMsg=err)
    # new imageprofile has a higher level, current level will be retained
    elif hostAcceptanceValue < targetAcceptanceValue:
        # no need to stop the upgrade, only log an info
        log.info('Host acceptance level %s will be retained after '
                 'upgrade.' % hostAcceptance)
    return Result('HOST_ACCEPTANCE', [True], [True])

RESULT_XML = '''\
    <test>
      <name>%(name)s</name>
      <expected>
        %(expected)s
      </expected>
      <found>
        %(found)s
      </found>
      <result>%(code)s</result>
    </test>
'''

def _marshalResult(result):
    intermediate = {
        'name': result.name,
        'expected': '\n        '.join([('<value>%s</value>' % str(exp))
                                       for exp in result.expected]),
        'found': '\n        '.join([('<value>%s</value>' % str(fnd))
                                    for fnd in result.found]),
        'code': result.code,
        }

    return RESULT_XML % intermediate

def resultsToXML(results):
    return '\n'.join([_marshalResult(result) for result in results])

output_xml = '''\
<?xml version="1.0"?>
<precheck>
 <info>
%(info)s
 </info>
 <tests>
%(tests)s
 </tests>
</precheck>
'''


def checkVsanV1Disks():
    '''
    vSAN wouldn't support vSAN v1 disks since 7.0U1 release, so this function
    prevent the customer from upgrading to ESXi version >= 7.0U1 if host has any
    vSAN v1 disks.

    vSAN v1 disk format has three partition, the second one is a vSAN metadata
    partition with partType 0xfa and the third one is a VMFS partition with
    partType 0xfb. Use following detection logic to check whether vSAN v1 disk
    presents.
    '''
    def _unwrap(ptrList):
       return [ptr.get() if hasattr(ptr, 'get') else ptr for ptr in ptrList]

    def _getVsanV1Disks():
        PARTITION_VSAN = 0xfa
        PARTITION_VMFS = 0xfb
        result = []
        disks = _unwrap(vmkctl.StorageInfoImpl().GetDiskLuns())
        for disk in disks:
            parts = _unwrap(disk.GetPartitions())
            partTypes = [part.GetPartitionType() for part in parts]
            if len(partTypes) == 3 and partTypes[1] == PARTITION_VSAN \
               and partTypes[2] == PARTITION_VMFS:
                result.append(disk.GetIdentifier())
        return result

    v1Disks = _getVsanV1Disks()
    errorMsg = 'vSAN v1 disks are not supported for upgrade'
    return Result('VSAN_V1_DISK', v1Disks, [], mismatchCode=Result.ERROR,
                  errorMsg=errorMsg)

def checkCvdsMigrationReadiness():
    '''
    Check the readiness to migrate from NVDS to CVDS by checking the value of
    property com.vmware.extraconfig.readyToMigrateToVds of distributed switches.
    If at least one occurrence of the key is set to 'false', then this check
    reports failure.
    The property can be missing or explicitly set to 'true' for a switch; in
    both cases the switch can migrate.
    '''
    TEST_NAME = 'CVDS_MIGRATION_READINESS'
    # Make sure net-dvs failure would fail the pipeline, and return code would
    # be 0 even if there is no matching line.
    CMD = (r'set -e && /sbin/net-dvs | '
           r'grep "com.vmware.extraconfig.readyToMigrateToVds" || true')
    try:
        out = run(CMD)
        outputRows = byteToStr(out).strip().splitlines()
    except Exception as e:
        err = 'Unable to get network DVS configuration: ' + str(e)
        log.error(err)
        return Result(TEST_NAME, [False], [True], errorMsg=err)

    for row in outputRows:
        if 'false' in row:
            err = ('ESXi host is not ready for NSX-T vSphere Distributed '
                   'Switch (VDS) migration included with this ESXi upgrade. '
                   'Please run Upgrade Readiness Tool (URT) from the NSX-T '
                   'Manager managing this host.')
            return Result(TEST_NAME, [False], [True], errorMsg=err)

    return Result(TEST_NAME, [True], [True])

#------------------------------------------------------------------------------
def checkDPUManaged():
    '''Check if host is managing dpu
    '''
    try:
       dpuList = runCli(['hardwareinternal', 'dpu', 'list'], True)
    except EsxcliError:
       dpuList = []
    dpuManaged = 0 if dpuList == [] else 1
    return Result("DPU_MANAGED", [dpuManaged], [1], comparator=operator.lt,
                  errorMsg="The target host manages DPU(s)",
                  mismatchCode=Result.ERROR)

#------------------------------------------------------------------------------

def _parseAndValidateCertificate(certFile):
    '''
    Parses and verifies the certificate file for all the certificates for the
    presence of SHA-1 signature. Returns the subject of the offending
    certificate with a SHA-1 signature.
    '''

    CERT_HEADER = '-----BEGIN CERTIFICATE-----'
    CERT_FOOTER = '-----END CERTIFICATE-----'

    certData = []
    result = True
    with open(certFile) as f:
        cert = None
        for line in f:
            if cert is None and CERT_HEADER not in line:
                continue
            if CERT_HEADER in line:
                cert = ""

            cert += line
            if CERT_FOOTER in line:
                certData.append(cert)
                cert = None

    subject = None
    for cert in certData:
        with tempfile.NamedTemporaryFile(mode='w') as temp:
            temp.write(cert)
            temp.flush()

            cmd = "openssl x509 -in %s -noout -text | " \
                  "grep 'Signature Algorithm'" % temp.name
            try:
                out = run(cmd)
                if b'sha1WithRSAEncryption' in out:
                    cmd = "openssl x509 -subject -noout -in %s " \
                          "-inform 'PEM'" % temp.name
                    out = run(cmd)
                    subject = out.decode().lstrip("subject=")
                    subject = subject.replace(", ", '/').rstrip('\n')
                    result = False
                    break
            except Exception as e:
                err = "Failed to parse certificate %s: %s" % (certFile, e)
                log.error(err)
                return False, None

    return result, subject

def _decryptLocalTgz(dest, encryptionFilePath,
                     localvePath, decryptedLocalPath):
    '''
    Decrypts and uncompresses local.tgz.ve file and provides access to the
    certs.
    '''
    # Disable includeKeyCache
    with open(encryptionFilePath) as f:
        lines = f.readlines()

    for i in range(len(lines)):
        if lines[i].startswith('includeKeyCache'):
            lines[i] = 'includeKeyCache = "FALSE"\n'
            break

    os.chmod(encryptionFilePath, 0o777)
    with open(encryptionFilePath, 'w') as f:
        for line in lines:
            f.write(line)

    # Stop and reinitialize keypersist service
    runCli(['--plugin-dir=/usr/lib/vmware/esxcli/int',
            'system', 'settings', 'encryption', 'stop'])
    runCli(['--plugin-dir=/usr/lib/vmware/esxcli/int',
            'system', 'settings', 'encryption', 'setup',
            '-c', encryptionFilePath])
    runCli(['--plugin-dir=/usr/lib/vmware/esxcli/int',
            'system', 'settings', 'encryption', 'start'])

    # Decrypt local.tgz.ve and save decrypted file as local.tgz
    decryptCmd = 'crypto-util ++coreDumpEnabled=false,mem=20 \
                 envelope extract --aad ESXConfiguration \
                 %s %s' % (localvePath, decryptedLocalPath)
    run(decryptCmd)

def checkCertSignAlgorithm():
    '''
    Checks the signature algorithm used in host certificates. Returns an error
    if weak signature algorithm is used.
    '''

    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        from systemStorage.bootbank import getBootbanksForInstall
        from weasel import userchoices

        bootDisk = userchoices.getEsxPhysicalDevice()

        # Get old bootbank and altbootbank paths
        oldAltBootbank, oldBootbank = getBootbanksForInstall(bootDisk)

        # Copy state.tgz in old bootbank into /tmp and work on the copy
        bbStateTgzPath = os.path.join(oldBootbank.path, 'state.tgz')
        destObj = tempfile.TemporaryDirectory()
        dest = destObj.name
        copyStateTgzPath = os.path.join(dest, 'state.tgz')
        if os.path.isfile(bbStateTgzPath):
            try:
                shutil.copy(bbStateTgzPath, copyStateTgzPath)

                # Extract state.tgz
                with tarfile.open(copyStateTgzPath) as tar:
                    tar.extractall(path=dest)

                # Check if state.tgz is encrypted
                localvePath = os.path.join(dest, 'local.tgz.ve')
                decryptedLocalPath = os.path.join(dest, 'local.tgz')
                encryptionFilePath = os.path.join(dest, 'encryption.info')
                if os.path.isfile(encryptionFilePath):
                    _decryptLocalTgz(dest, encryptionFilePath,
                                     localvePath, decryptedLocalPath)
            except (EsxcliError, Exception) as e:
                err = "Failed to validate signature type of host " \
                      "certificates: %s" % e
                log.error(err)
                destObj.cleanup()
                return Result("SHA1_CERT", [False], [True], errorMsg=err,
                              mismatchCode=Result.ERROR)

            # Untar local.tgz
            with tarfile.open(decryptedLocalPath) as tar:
                tar.extractall(path=dest)

    # Check the certs for weak signature algorithms.
    certs = ['castore.pem', 'rui.crt', 'vsan_kms_castore.pem',
             'vsan_kms_client.crt', 'vsan_kms_castore_old.pem',
             'vsan_kms_client_old.crt']

    certPath = 'etc/vmware/ssl/'
    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        certPath = os.path.join(dest, certPath)
    else:
        certPath = os.path.join('/', certPath)

    found = []
    ERR_MSG = ("SHA-1 signature found in host certificate %s with subject %s. "
               "Support for certificates with weak signature algorithm SHA-1 "
               "has been removed in ESXi 8.0. To proceed with upgrade, replace "
               "it with a SHA-2 signature based certificate. Refer to release "
               "notes and KB 89424 for more details.")

    err = ''
    parseFailure = False
    for cert in certs:
        if os.path.isfile(os.path.join(certPath, cert)):
            result, subject = _parseAndValidateCertificate(os.path.join(certPath, cert))
            if not result:
                if subject:
                    certInfo = cert + '(' + subject + ')'
                    found = [certInfo]
                    err = ERR_MSG % (cert, subject)
                else:
                    err = "Failed to validate signature type of certificate " \
                          "%s" % cert
                    parseFailure = True
                break

    # Cleanup the temp directory
    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        destObj.cleanup()

    if parseFailure:
        return Result("SHA1_CERT", [False], [True], errorMsg=err,
                      mismatchCode=Result.ERROR)

    return Result("SHA1_CERT", found, [], errorMsg=err,
                  mismatchCode=Result.ERROR)

#------------------------------------------------------------------------------
def checkTpmVersion():
    '''
    Check the current TPM version on the hardware.
    If the current version is '1', then this check throws a warning.
    '''
    from vmware import vsi
    if vsi.get("/hardware/tpm/present") == 1 and vsi.get('/hardware/tpm/version') == 1:
        errorMsg = ('TPM 1.2 device detected. Support for TPM version 1.2 is '
                    'discontinued. Installation may proceed, but may cause the '
                    'system to behave unexpectedly.')
        return Result('TPM_VERSION', [False], [True],
                    errorMsg=errorMsg,
                    mismatchCode=Result.WARNING)
    else:
        return Result('TPM_VERSION', [True], [True])


#------------------------------------------------------------------------------
def checkStorageEntropyCache():
    '''
    Check if the storage entropy cache is full. If not, then return an error.
    '''
    from entropy import (checkEntropyCache, EntropyError, ENTROPY_TARDISK_NAME,
        STORAGE_ENTROPY_CACHE)

    err = None
    cacheFile = STORAGE_ENTROPY_CACHE

    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        from systemStorage.bootbank import getBootbanksForInstall
        from weasel import userchoices

        bootDisk = userchoices.getEsxPhysicalDevice()
        _, oldBootbank = getBootbanksForInstall(bootDisk)

        bbTgzPath = os.path.join(oldBootbank.path, ENTROPY_TARDISK_NAME)

        if not os.path.isfile(bbTgzPath):
            # no storage entropy cache exists, so nothing to check
            return Result('ENTROPY_CACHE', [True], [True])

        destObj = tempfile.TemporaryDirectory()
        dest = destObj.name

        try:
            with tarfile.open(bbTgzPath) as tar:
                tar.extractall(path=dest)
        except Exception as e:
            err = "Failed to check storage entropy cache usage : %s" % e
            log.error(err)
            destObj.cleanup()
            return Result("ENTROPY_CACHE", [False], [True], errorMsg=err,
                          mismatchCode=Result.ERROR)
        cacheFile = os.path.join(dest, STORAGE_ENTROPY_CACHE)

    try:
        checkEntropyCache(cacheFile=cacheFile)
    except EntropyError as e:
        log.error(e)
        err = ('Storage entropy cache is not full. A full entropy cache is '
               'required for upgrade. Refer to KB 89854 for steps on how to '
               'refill the cache.')

    if systemProbe.environment == SystemProbeESXi.WEASEL_ENV:
        destObj.cleanup()

    if err:
        return Result('ENTROPY_CACHE', [False], [True], errorMsg=err,
                      mismatchCode=Result.ERROR)
    else:
        return Result('ENTROPY_CACHE', [True], [True])


#------------------------------------------------------------------------------
def checkSphereletVersion():
    """Check the Spherelet version is compatible with the new ESXi version.
    """
    # See PR 3025362, Spherelet below 1.3.3 need to be warned, except newer
    # 1.3.0 builds.
    VER_130 = Version.Version('1.3.0')
    MIN_130_RELEASE = Version.Version('19862097')
    VER_133 = Version.Version('1.3.3')
    ERR_MSG = ('Spherelet version %s is not compatible with ESXi 8.0 and later '
               'version. Please upgrade your WCP cluster to install a '
               'compatible Spherelet version, or remove Spherelet if the host '
               'is not in a WCP cluster.')

    found = []
    for vib in systemProbe.targetImageProfile.vibs.values():
        if vib.name == 'spherelet':
            version, release = vib.version.version, vib.version.release
            if ((version == VER_130 and release < MIN_130_RELEASE) or
                    (version < VER_133 and version != VER_130)):
                found = [str(vib.version)]
            break

    errMsg = (ERR_MSG % found[0]) if found else ''
    return Result('SPHERELET_VERSION', found, [], errorMsg=errMsg,
                  mismatchCode=Result.WARNING)

#------------------------------------------------------------------------------
systemProbe = None
options = None

def init(environment, freshInstall, keepDatastore=False, hostImageProfile=None,
         targetImageProfile=None):
    '''Initiate systemProbe for precheck.
       Parameters:
          environment        - one of WEASEL_ENV, VUM_ENV, ESXCLI_ENV from
                               SystemProbeESXi class to indicate where precheck
                               is running, affects localtion to load metadata
                               and behavior of some precheck items.
          freshInstall       - set to True for fresh install.
          keepDatastore      - set to True when preserving VMFS in weasel.
          hostImageProfile   - the image profile on the host; passed in by
                               Image Manager during a scan.
          targetImageProfie  - the final image profile to run on the host;
                               passed in by esxcli for VmkLinux tests and
                               Image Manager during a scan.
    '''
    global systemProbe
    if environment == SystemProbeESXi.WEASEL_ENV:
        from weasel import userchoices
        # For ISO, the device to be installed/upgraded
        bootDeviceName = userchoices.getEsxPhysicalDevice()
        keepDatastore = userchoices.getPreserveVmfs()
        if freshInstall:
            # For fresh install, there is no need to load old VIBs, and thus
            # we don't need to pass partition paths to SystemProbe.
            # Also, for a blank disk the Cache() init will fail.
            systemProbe = SystemProbeESXi(environment,
                                          freshInstall=freshInstall,
                                          keepDatastore=keepDatastore,
                                          bootDeviceName=bootDeviceName)
        else:
            from weasel import cache
            bootbank, _, locker = cache.getEsxPartPaths(bootDeviceName)
            # Supply old bootbank and locker path for loading host VIBs
            systemProbe = SystemProbeESXi(environment,
                                          freshInstall=freshInstall,
                                          keepDatastore=keepDatastore,
                                          bootDeviceName=bootDeviceName,
                                          hostBootbankPath=bootbank,
                                          hostLockerPath=locker)
    else:
        # Otherwise the current boot device
        bootDeviceName = vmkctl.SystemInfoImpl().GetBootDevice()
        # Host VIBs will be loaded from the live database if not given
        systemProbe = SystemProbeESXi(environment,
                                      freshInstall=freshInstall,
                                      bootDeviceName=bootDeviceName,
                                      hostImageProfile=hostImageProfile,
                                      targetImageProfile=targetImageProfile)

def upgradeAction():
    '''This function is called during the Weasel process in the install
    environment.  It runs through the checks that would make sense there.
    returns None if everything went smoothly, or a string containing all
    the errors if not.
    '''
    # These modules are expected to be unavailable when upgrade_precheck
    # is run from the command line, so import them only when inside the
    # upgradeAction function - it is invoked by Weasel code, so Weasel
    # modules will be available.
    from weasel import userchoices

    log.info('Starting the precheck tests for upgrade')
    init(SystemProbeESXi.WEASEL_ENV, False)

    tests = [
        checkUpgradePath,
        checkMemorySize,
        checkCpuSupported,
        checkCpuCores,
        checkBiosFirmwareType,
        checkExtraCpuLicenseRequired,
        checkHostHw,
        checkUnsupportedDevices,
        checkVMFSVersion,
        checkImageProfileSize,
        checkVsanV1Disks,
        checkCvdsMigrationReadiness,
        checkTpmVersion,
        checkVibChecksum,
        checkSphereletVersion,
        checkCertSignAlgorithm,
        checkStorageEntropyCache,
        validateVFATPartitions,
        checkBootDiskSize,
        ]

    # only check for vib conflicts if force migrate has not been selected
    if not userchoices.getForceMigrate():
        tests.append(checkVibConflicts)
        tests.append(checkVibDependencies)

    results = [testFn() for testFn in tests]
    return humanReadableResultBlurbs(results)

def installAction():
    '''This function is called during the Weasel process in the install
    environment.  It runs through the checks that would make sense there.
    returns None if everything went smoothly, or a string containing all
    the errors if not.
    '''
    log.info('Starting the precheck tests for install')
    init(SystemProbeESXi.WEASEL_ENV, True)

    tests = [
         checkMemorySize,
         checkCpuSupported,
         checkHardwareVirtualization,
         checkCpuCores,
         checkBiosFirmwareType,
         checkLAHFSAHF64bitFeatures,
         checkNXbitCpuFeature,
         checkHostHw,
         checkUnsupportedDevices,
         checkVMFSVersion,
         checkImageProfileSize,
         checkVsanV1Disks,
         checkTpmVersion,
         checkVibChecksum,
         checkBootDiskSize,
        ]

    results = [testFn() for testFn in tests]
    return humanReadableResultBlurbs(results)

def cliUpgradeAction(targetImageProfile=None, vmkLinuxOnly=False):
    '''This function is called during localcli/esxcli software profile install
       and update calls.
       Without targetImageProfile, this function executes only upgrade path
       and hardware checks.
       Otherwise, if vmkLinuxOnly is set, only execute VmkLinux checks, needed
       for 6.7 upgrades, or execute both regular and VmkLinux checks.
       This function returns a two-tuple of error and warning string, or two
       empty strings if everything was okay.
    '''
    log = logging.getLogger('precheck')

    # freshInstall flag does not mean anything to esxcli environment as the only
    # metadata needed is targetImageProfile.
    init(SystemProbeESXi.ESXCLI_ENV, False,
         targetImageProfile=targetImageProfile)

    regularTests = [
        checkUpgradePath,
        checkMemorySize,
        checkCpuSupported,
        checkCpuCores,
        checkBiosFirmwareType,
        checkUnsupportedDevices,
        checkBootDiskSize,
        checkVsanV1Disks,
        checkCvdsMigrationReadiness,
        checkTpmVersion,
        checkCertSignAlgorithm,
        checkStorageEntropyCache,
        validateVFATPartitions,
        ]

    # The following tests require the target image profile to run and hence
    # are to be run only when the vmkLinuxOnly flag is set to True
    targetRequiredTests = [
        checkBootNicIsNative,
        checkBootbankDeviceIsNative,
        checkSphereletVersion,
        ]

    if targetImageProfile is None:
        log.info('Starting precheck for localcli/esxcli, no VmkLinux checks')
        tests = regularTests
    elif vmkLinuxOnly:
        log.info('Starting precheck for localcli/esxcli, VmkLinux checks only')
        tests = targetRequiredTests
    else:
        log.info('Starting precheck for localcli/esxcli, all checks.')
        tests = regularTests + targetRequiredTests

    results = [testFn() for testFn in tests]

    # Result will have warning and override message combined
    return humanReadableResultBlurbs(results, combineWarnAndOverride=True)

def imageManagerAction(hostProfile, targetProfile):
    """This function is called during a image manager (personality manager)
       scan to conduct prechecks.
       Input: the current host image profile and the image profile converted
       from the desired software spec.
       Return: two lists of error and warning result objects, they will be
       converted to proper messages/notifications by the caller.
    """
    log = logging.getLogger('precheck')

    # "esxcli" env means no initialization is done to fetch metadata other
    # than the input host and target image profiles.
    # freshInstall flag does not mean anything to esxcli environment.
    init(SystemProbeESXi.ESXCLI_ENV, False,
         hostImageProfile=hostProfile,
         targetImageProfile=targetProfile)

    tests = [
        checkMemorySize,
        checkCpuSupported,
        checkCpuCores,
        checkBiosFirmwareType,
        checkUnsupportedDevices,
        checkHostHw,
        checkBootNicIsNative,
        checkBootbankDeviceIsNative,
        checkImageProfileSize,
        checkLockerSpaceAvail,
        checkBootDiskSize,
        checkHostAcceptance,
        checkVsanV1Disks,
        checkTpmVersion,
        checkVibChecksum,
        checkSphereletVersion,
        checkCertSignAlgorithm,
        validateVFATPartitions,
        ]

    # Entropy precheck which checks for cache size, needs to run for vLCM only
    # when a drift exists and there is a possibility of remediation.
    # If it runs as part of all prechecks, it creates an issue
    # for the scan performed after remediation because the cache is never
    # full after reboot.
    if not hostProfile.HasSameInventory(targetProfile):
        tests += [checkStorageEntropyCache]
    else:
        log.info('Skipping entropy precheck')

    log.info('Starting precheck for image manager.')

    errors, warnings = list(), list()
    for testFn in tests:
        result = testFn()
        if result.code == result.ERROR:
            errors.append(result)
        elif result.isWarnType():
            warnings.append(result)

    return errors, warnings

def humanReadableResultBlurbs(results, combineWarnAndOverride=False):

    warningFailures = ''
    errorFailures = ''
    overrideFailures = ''
    errorNewLineNeeded = False
    warningNewLineNeeded = False
    overrideNewLineNeeded = False
    for result in results:
        if not result:
            if result.code == Result.ERROR:
                if errorNewLineNeeded:
                    errorFailures += '\n\n'
                errorFailures += str(result)
                errorNewLineNeeded = True
            elif result.code == Result.OVERRIDEWARNING:
                if overrideNewLineNeeded:
                    overrideFailures += '\n\n'
                overrideFailures += str(result)
                overrideNewLineNeeded = True
            else:
                if warningNewLineNeeded:
                    warningFailures += '\n\n'
                warningFailures += str(result)
                warningNewLineNeeded = True

    if errorFailures != '':
        log.error('Precheck Error(s). \n %s' % errorFailures)
    if warningFailures != '' or overrideFailures != '':
        log.warn('Precheck Warnings(s). \n %s'
              % warningFailures + overrideFailures + '\n')
    if combineWarnAndOverride:
        return errorFailures, warningFailures + overrideFailures
    else:
        return errorFailures, warningFailures, overrideFailures

def main(argv):
    '''Main precheck function for VUM.
    '''
    global options
    parser = optparse.OptionParser()
    parser.add_option('--ip', dest='ip', default='',
                      help=('The IP address that the host should bring up'
                            ' after rebooting.'))

    options, args = parser.parse_args()

    results = [checkInitializable()]

    if not results[0]:
        testsSection = resultsToXML(results)
        print(output_xml % {
                            'info': '',
                            'tests': testsSection,
                           })
        return 0

    init(SystemProbeESXi.VUM_ENV, False)

    # Before checking the available space on disk, let us first check if host
    # is in maintenance mode.
    # Otherwise checkAvailableSpaceForISO will be skipped.
    tests = [checkAvailableSpaceForISO,] if HostInfo.GetMaintenanceMode() else []

    tests += [
        checkMemorySize,
        checkCpuSupported,
        checkCpuCores,
        checkSaneEsxConf,
        checkUnsupportedDevices,
        checkHostHw,
        checkUpdatesPending,
        checkVMFSVersion,
        checkBootNicIsNative,
        checkBootbankDeviceIsNative,
        checkVibConflicts,
        checkVibDependencies,
        checkImageProfileSize,
        checkLockerSpaceAvail,
        checkBootDiskSize,
        checkHostAcceptance,
        checkVsanV1Disks,
        checkCvdsMigrationReadiness,
        checkTpmVersion,
        checkVibChecksum,
        checkDPUManaged,
        checkSphereletVersion,
        checkCertSignAlgorithm,
        validateVFATPartitions,
        ]

    results += [testFn() for testFn in tests]

    # Run checkPackageCompliance separately so that its result can be used to
    # determine additional tests required to run.
    complianceResult = checkPackageCompliance()
    results += [complianceResult]

    # Entropy precheck which checks for cache size, needs to run only
    # when image is not compliant and there is a possibility of remediation.
    # If it runs as part of all prechecks, it can create an issue
    # for the scan performed after remediation because the cache is never
    # full after reboot.
    if complianceResult.code != Result.SUCCESS:
        results += [checkStorageEntropyCache()]

    # Delete ramdisk created to check memory availability during scan.
    # Remediation will recreate the ramdisk.
    deallocateRamDisk(RAMDISK_NAME)

    testsSection = resultsToXML(results)

    print(output_xml % {
                        'info': '',
                        'tests': testsSection,
                        })

    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
    #import doctest
    #doctest.testmod()
