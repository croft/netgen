#!/usr/bin/env python

import graphviz
import ipaddr
import netaddr
import os
import re
import socket
import struct

# TODO: replace with actual OF values
OFPFC_ADD = 0
OFPFC_DELETE_STRICT = 1

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
    if wc == 0:
        return int2ip(int("1"*32, 2))

    return int2ip(int("1"*32, 2) ^ int("1"*wc, 2))

def mac_to_binstr(mac):
    return netaddr.EUI(mac).bits().replace("-", "")

def mac2int(mac):
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
        self.addField("DL_SRC", 48, int(0xFFFFFFFFFFFF), mac2int)
        self.addField("DL_DST", 48, int(0xFFFFFFFFFFFF), mac2int)
        self.addField("DL_TYPE", 16, int(0xFFFF))
        self.addField("NW_SRC", 32, int(0xFFFFFFFF), ip2int)
        self.addField("NW_DST", 32, int(0xFFFFFFFF), ip2int)

HeaderField = PacketField()

class PacketClass(object):
    def __init__(self, fname=None, idx=None):
        self.idx = idx
        if fname is None:
            self.edges = {}
        else:
            self.edges = Topology.get_edges(fname, 1)

    def original_dest(self, network):
        dest = {}
        egress = network.topo.egresses()
        for src in network.topo.switches.keys():
            if src in egress:
                dest[src] = src
                continue

            temp = src
            while temp in self.edges:
                temp = self.edges[temp]
                if temp in egress:
                    dest[src] = temp

        return dest

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

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "\n".join("{0} {1} {2}".format(self.idx, k,v) for k,v in self.edges.iteritems())

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

class Node(object):
    def __init__(self, ip=None, mac=None, name=None):
        self.ip = ip
        self.mac = mac
        self.name = name

class Switch(Node):
    def __init__(self, ip=None, mac=None, name=None):
        self.ft = []
        super(Switch, self).__init__(ip, mac, name)

class Host(Node):
    def __init__(self, ip=None, mac=None, name=None):
        self.ft = []
        super(Host, self).__init__(ip, mac, name)

class FlowEntry(object):
    def __init__(self, dest, wildcard, location, nexthops, priority=1, src=None):
        if not isinstance(nexthops, list):
            nexthops = [nexthops]

        self.dest = dest
        self.src = src
        self.wildcard = wildcard
        self.location = location
        self.nexthops = nexthops
        self.priority = priority

    def __repr__(self):
        return str(self)

    def __str__(self):
        if len(self.nexthops) == 0:
            nhops = "-"
        else:
            nhops = ",".join(self.nexthops)

        return "- - {0} {1} {2} {3} - {4}".format(self.dest,
                                                  self.wildcard,
                                                  self.location,
                                                  nhops,
                                                  self.priority)

class Topology(object):
    def __init__(self):
        self.switches = {}
        self.hosts = {}
        self.edges = {}
        self.paths = {}
        self.egress = []

    @property
    def strrepr(self):
        return {v: k for k,v in self.intrepr.items()}

    @property
    def intrepr(self):
        count = 1
        alias = {}
        for name in sorted(self.nodes.keys()):
            alias[name] = count
            count += 1

        return alias

    # TODO: better perf?
    @property
    def nodes(self):
        n = self.switches.copy()
        n.update(self.hosts)
        return n

    def egresses(self):
        # if manually defined
        if len(self.egress) > 0:
            return self.egress

        # otherwise, any switch with switch degree 1 or
        # connected to a host
        e = []
        for s in self.switches.keys():
            if len(self.edges[s]) == 1:
                e.append(s)
                continue

            for neighbor in self.edges[s]:
                if neighbor in self.hosts:
                    e.append(s)
                    break

        return e

    def iter_edges(self):
        out = []
        written = []
        for src in sorted(self.edges.keys()):
            for dst in self.edges[src]:
                if (dst, src) not in written:
                    written.append((src, dst))
        return written

        with open(os.path.join(dest_dir, topofile), 'w') as f:
            f.writelines(out)


    def make_configmap(self, dest_dir, mapfile="config.map"):
        out = []
        for switch in self.switches.keys():
            out.append("R R{0}\n".format(switch))
        with open(os.path.join(dest_dir, mapfile), 'w') as f:
            f.writelines(out)

    def make_topofile(self, dest_dir, topofile="topo.txt"):
        out = []
        written = []
        for src, dsts in self.edges.iteritems():
            for dst in dsts:
                if (dst,src) not in written:
                    out.append("{0} {1}\n".format(dst, src))
                    written.append((src, dst))

        with open(os.path.join(dest_dir, topofile), 'w') as f:
            f.writelines(out)

    def make_rocketfile(self, dest_dir):
        for sw in self.switches.values():
            with open(os.path.join(dest_dir, "R_" + sw.name), 'w') as f:
                f.write("\n".join([str(flow) for flow in sw.ft]))

    def make_graph(self, dest_dir, graphfile="topo.gv"):
        g = graphviz.Graph(format='svg')
        for node in self.hosts.keys() + self.edges.keys():
            g.node(node)

        added = []
        for src, dsts in self.edges.iteritems():
            for dst in dsts:
                if (src,dst) not in added:
                    g.edge(src, dst)
                    added.append((dst, src))

        g.render(os.path.join(dest_dir, graphfile))

    def switch_diff(self, diff):
        if not isinstance(diff, list):
            diff = [diff]

        return [s for s in self.switches.keys() if s not in diff]

