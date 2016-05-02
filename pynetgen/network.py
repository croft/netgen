#!/usr/bin/env python

import graphviz
import ipaddr
import netaddr
import os
import re
import socket
import struct

import trie

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

# TODO: use one data structure for both
# TODO: add mask to flowtable
def ft2rules(loc, ft):
    rules = []
    for flow in ft:
        r = trie.Rule()
        r.ruleType = trie.Rule.FORWARDING

        if flow.src is not None:
            r.fieldValue[HeaderField.Index["NW_SRC"]] = ip2int(flow.src)
            r.fieldMask[HeaderField.Index["NW_SRC"]] = ip2int("255.255.255.255")

        if flow.dest is not None:
            r.fieldValue[HeaderField.Index["NW_DST"]] = ip2int(flow.dest)
            r.fieldMask[HeaderField.Index["NW_DST"]] = ip2int("255.255.255.255")

        r.priority = flow.priority

        # TODO: how to handle multiple next hops?
        r.nextHop = flow.nexthops[0]

        r.location = loc
        rules.append(r)

    return rules

# TODO: use one data structure for both
def graph2pc(i, fg):
    classes = []
    pc = PacketClass(idx=i)
    for name, link in fg.links.iteritems():
        if len(link) > 1:
            raise Exception("Don't know yet how to handle multiple links?")
        pc.edges[name] = link[0].rule.nextHop

    if len(pc.edges) == 0:
        return None

    return pc

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
    def __init__(self, idx=None):
        self.idx = idx
        self.edges = {}

    def iteredges(self):
        e = []
        for src, dsts in self.edges.iteritems():
            if not isinstance(dsts, list):
                dsts = [dsts]
            for dst in dsts:
                e.append((src, dst))
        return e

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
    def __init__(self, topo):
        self.topo = topo
        self.classes = {}
        self._compute_classes()

    def _compute_classes(self):
        mtrie = trie.MultilevelTrie()
        for switch in self.topo.switches.values():
            for rule in ft2rules(switch.name, switch.ft):
                mtrie.addRule(rule)

        eqclasses = mtrie.getAllEquivalenceClasses()
        for ptrie, pclass in eqclasses:
            idx = len(self.classes) + 1
            graph = mtrie.getForwardingGraph(ptrie, pclass)
            pc = graph2pc(idx, graph)
            if pc is not None:
                self.classes[idx] = pc

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

    def write_debug_output(self, data_dir="data"):
        if os.path.exists(data_dir):
            shutil.rmtree(data_dir)

        os.makedirs(data_dir)
        topo.make_topofile(data_dir)
        topo.make_rocketfile(data_dir)
        topo.make_graph(data_dir)
        topo.make_configmap(data_dir)

    def iteredges(self):
        e = []
        for src, dsts in self.edges.iteritems():
            if not isinstance(dsts, list):
                dsts = [dsts]
            for dst in dsts:
                e.append((src, dst))
        return e

    # TODO: make property, hide manually defined egresses self.egress
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

