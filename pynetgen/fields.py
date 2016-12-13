#/usr/bin/env python

import ipaddr
import netaddr
import re
import socket
import struct

OFPFC_ADD = 0
OFPFC_DELETE_STRICT = 4

def ip2int(ip):
    # handle default value
    if ip == "0":
        return 0
    return int(ipaddr.IPv4Address(ip))

def int2ip(i):
    return socket.inet_ntoa(struct.pack("!I", i))

def int2mac(mac):
    h = "{0:#0{1}x}".format(mac, 12)[2:]
    return ':'.join(s.encode('hex') for s in h.decode('hex'))

def wc2ip(wc):
    wc = 32-wc
    if wc == 0:
        return int2ip(int("1"*32, 2))

    return int2ip(int("1"*32, 2) ^ int("1"*wc, 2))

def mask2wc(mask):
    octets = mask.split(".")
    binary_str = ''
    for octet in octets:
        binary_str += bin(int(octet))[2:].zfill(8)
    return len(binary_str.rstrip('0'))

def mac_to_binstr(mac):
    return netaddr.EUI(mac).bits().replace("-", "")

def mac2int(mac):
    # handle default value
    if mac == "0":
        return 0
    return int(mac_to_binstr(mac))

def is_ip(ip):
    r = re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", ip)
    return r is not None

class FieldDefinition(object):
    def __init__(self):
        self.Index = {}
        self.Width = {}
        self.MaxValue = {}
        self.intConverter = {}
        self.count = 0

    def addField(self, name, width, maxvalue, intfunc=None):
        index = self.count
        self.Index[name] = index
        self.Index[index] = name
        self.Width[index] = width
        self.MaxValue[index] = maxvalue
        if intfunc is None:
            self.intConverter[index] = FieldDefinition.defaultConverter
        else:
            self.intConverter[index] = intfunc
        self.count += 1

    @classmethod
    def defaultConverter(cls, val):
        return int(val)

    @property
    def End(self):
        return self.count

    def intValue(self, index, value):
        if isinstance(value, int):
            return value
        return self.intConverter[index](value)

class PacketField(FieldDefinition):
    def __init__(self):
        super(PacketField, self).__init__()
        self.addField("IN_PORT", 16, int(0xFFFF))
        self.addField("DL_SRC", 48, int(0xFFFFFFFFFFFF), mac2int)
        self.addField("DL_DST", 48, int(0xFFFFFFFFFFFF), mac2int)
        self.addField("DL_TYPE", 16, int(0xFFFF))
        self.addField("NW_SRC", 32, int(0xFFFFFFFF), ip2int)
        self.addField("NW_DST", 32, int(0xFFFFFFFF), ip2int)

HeaderField = PacketField()
