#!/usr/bin/env python

import ipaddr
import socket
import struct
from netaddr import *

import argparse
import os
import random
import re
import shutil
import string
import ConfigParser

import FAdo.reex
from FAdo.reex import *

# TODO: replace with actual OF values
OFPFC_ADD = 0
OFPFC_DELETE_STRICT = 1

def iptoi(ip):
    # handle default value
    if ip == "0":
        return 0
    return int(ipaddr.IPv4Address(ip))

def itoip(i):
    return socket.inet_ntoa(struct.pack("!I", i))

def mac_to_binstr(mac):
    return EUI(mac).bits().replace("-", "")

def mactoi(mac):
    # handle default value
    if mac == "0":
        return 0
    return int(mac_to_binstr(mac))

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
        return self.intConverter[index](value)

class PacketField(FieldDefinition):
    def __init__(self):
        super(PacketField, self).__init__()
        self.addField("IN_PORT", 16, int(0xFFFF))
        self.addField("DL_SRC", 48, int(0xFFFFFFFFFFFF), mactoi)
        self.addField("DL_DST", 48, int(0xFFFFFFFFFFFF), mactoi)
        self.addField("DL_TYPE", 16, int(0xFFFF))
        self.addField("NW_SRC", 32, int(0xFFFFFFFF), iptoi)
        self.addField("NW_DST", 32, int(0xFFFFFFFF), iptoi)

HeaderField = PacketField()

# TODO: merge network.topo and topos.topo
class Topology(object):
    def __init__(self, fname):
        self.edges = Topology.get_edges(fname)

        # TODO: better way to filter hosts, combine keys+values
        self.switches = [s for s in self.edges.keys() if s[0] != 'h'] + \
                        [s for s in self.edges.values() if s[0] != 'h']
        self.switches = list(set(self.switches))

    @classmethod
    def get_edges(cls, fname, offset=0):
        edges = {}
        with open(fname) as f:
            for line in f.readlines():
                tokens = line.strip().split()
                edges[tokens[offset]] = tokens[offset+1]

        return edges

    def switch_diff(self, diff):
        if not isinstance(diff, list):
            diff = [diff]

        return [s for s in self.switches if s not in diff]

class PacketClass(object):
    def __init__(self, fname=None):
        if fname is None:
            self.edges = {}
        else:
            self.edges = Topology.get_edges(fname, 1)

    def construct_strings(self):
        strings = []
        for key in self.edges.keys():
            s = []
            term = key
            while term in self.edges.keys():
                s.append(term)
                term = self.edges[term]

            s.append(term)
            strings.append(" ".join(s))

        return strings

class Network(object):
    def __init__(self, class_dir=None):
        self.classes = {}
        self.class_files = {}
        self.topo = None

        if class_dir is None:
            return

        files = [os.path.join(class_dir, f) for f in os.listdir(class_dir)
                 if os.path.isfile(os.path.join(class_dir, f))
                 and os.path.splitext(f)[1] == '.txt'
                 and f != "topo.txt"]

        if not os.path.isfile(os.path.join(class_dir, "topo.txt")):
            raise Exception("Missing {0} file"
                            .format(os.path.join(class_dir, "topo.txt")))

        self.topo = Topology(os.path.join(class_dir, "topo.txt"))

        for f in files:
            fname = os.path.splitext(os.path.basename(f))[0]
            self.classes[fname] = PacketClass(f)
            self.class_files[fname] = f

    def match_classes(self, regex):
        matches = []
        for p, pc in self.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    matches.append(p)
                    break

        return sorted(matches, key=int)
