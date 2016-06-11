#!/usr/bin/env python

import fnss
import math
import multiprocessing
import networkx
import os
import pickle
import random

from utils.load_stanford_backbone import *
from utils.load_internet2_backbone import *
from headerspace.applications import *
from headerspace.hs import *
from headerspace.tf import *
from config_parser.cisco_router_parser import ciscoRouter
from config_parser.juniper_parser import juniperRouter
from config_parser.transfer_function_to_openflow import OpenFlow_Rule_Generator

import trie
from fields import HeaderField, int2mac, ip2int, int2ip, wc2ip
from log import logger
from network import Topology, Switch, Host, FlowEntry, pairwise, PacketClass

class TfTopology(Topology):
    def __init__(self, definition, ntf, ttf, port_ids, router):
        super(TfTopology, self).__init__()
        self.definition = definition
        self.ntf = ntf()
        self.ttf = ttf()
        self.port_map, self.port_reverse_map = port_ids()
        self.router = router(1)
        self.edge_ports = set()
        self.intfs = {}
        edge_port_ips = {}
        start_ip = ip2int("10.0.0.1")

        # keys (ports) should be ints
        self.port_reverse_map = dict((int(k), v) for (k, v) in
                                     self.port_reverse_map.iteritems())

        for rtr1, intf1, rtr2, intf2 in self.definition:
            if rtr1 not in self.intfs:
                self.intfs[rtr1] = {}
            if rtr2 not in self.intfs:
                self.intfs[rtr2] = {}

            if rtr1 not in self.edges:
                self.edges[rtr1] = []
            if rtr2 not in self.edges:
                self.edges[rtr2] = []

            self.intfs[rtr1][intf1] = rtr2
            self.intfs[rtr2][intf2] = rtr1
            self.edges[rtr1].append(rtr2)
            self.edges[rtr2].append(rtr1)
            self.switches[rtr1] = Switch(name=rtr1)
            self.switches[rtr2] = Switch(name=rtr2)

        for rtr in self.port_map.keys():
            for port in self.port_map[rtr].values():
                self.edge_ports.add(int(port) +
                                    self.router.PORT_TYPE_MULTIPLIER *
                                    self.router.OUTPUT_PORT_TYPE_CONST)

        for port in sorted(self.edge_ports):
            edge_port_ips[port] = int2ip(start_ip + len(edge_port_ips))

        for tf in self.ntf.tf_list:
            ofg = OpenFlow_Rule_Generator(tf, self.router.HS_FORMAT())
            rules = ofg.generate_of_rules()
            swname = tf.prefix_id

            for rule in rules:
                #dest = int2ip(rule['ip_dst_match'])
                #wc = wc2ip(rule['ip_dst_wc'])
                outports = rule['out_ports']
                location = tf.prefix_id
                nexthops = []

                for port in outports:
                    if port in self.edge_ports:
                        nexthops.append(edge_port_ips[port])
                        pass
                    else:
                        p = port - self.router.PORT_TYPE_MULTIPLIER
                        if p in self.port_reverse_map.keys():
                            portname = self.port_reverse_map[p].split("-")[1]
                            if portname in self.intfs[location].keys():
                                nexthop = self.intfs[location][portname]
                                nexthops.append(nexthop)
                            else:
                                # TODO
                                pass

                r = trie.Rule()
                r.ruleType = trie.Rule.FORWARDING
                r.location = location
                r.priority = 1

                # TODO: handle multipath
                if len(nexthops) > 0:
                    r.nextHop = nexthops[0]

                nw_dst_match = rule['ip_dst_match']
                nw_dst_wc = ip2int(wc2ip(rule['ip_dst_wc']))
                nw_src_match = rule['ip_src_match']
                nw_src_wc = ip2int(wc2ip(rule['ip_src_wc']))

                r.fieldValue[HeaderField.Index["NW_DST"]] = nw_dst_match
                r.fieldMask[HeaderField.Index["NW_DST"]] = nw_dst_wc
                r.fieldValue[HeaderField.Index["NW_SRC"]] = nw_src_match
                r.fieldMask[HeaderField.Index["NW_SRC"]] = nw_src_wc

                # filter inports - only add edge inports
                inports = [(p + router.PORT_TYPE_MULTIPLIER) for p
                           in rule['in_ports']
                           if (p + router.PORT_TYPE_MULTIPLIER)
                           in self.edge_ports]

                if len(inports) > 0:
                    r.fieldValue[HeaderField.Index["IN_PORT"]] = sorted(inports)[0]

                # TODO: handle vlan rewrite?
                # r.fieldValue[HeaderField.Index["DL_VLAN"]] = rule['vlan_match']
                # flow = FlowEntry(dest=dest,
                #                  wildcard=wc,
                #                  location=location,
                #                  nexthops=nexthops)

                if len(nexthops) > 1:
                    print "Can't handle multiple next hops", nexthops

                if len(nexthops) > 0:
                    # self.switches[swname].ft.append(flow)
                    self.switches[swname].ft.append(r)

    def get_pc_ingress(self, pc):
        ingress = []
        for location, links in pc.graph.links.iteritems():
            for link in links:
                inport = link.rule.fieldValue[HeaderField.Index["IN_PORT"]]
                if inport in self.edge_ports:
                    ingress.append(location)
                    break

        return ingress

    def get_pc_egress(self, pc):
        egress = []
        for location, links in pc.graph.links.iteritems():
            for link in links:
                if link.rule.nextHop not in self.nodes:
                    egress.append(location)
                    break

        return egress

class Internet2Topo(TfTopology):
    Definition = [("chic","xe-0/1/0","newy32aoa","xe-0/1/3"), #05667
                  ("chic","xe-1/0/1","kans","xe-0/1/0"), #05568
                  ("chic","xe-1/1/3","wash","xe-6/3/0"), #05250
                  ("hous","xe-3/1/0","losa","ge-6/0/0"), #05559
                  ("kans","ge-6/0/0","salt","ge-6/1/0"), #05138
                  ("chic","xe-1/1/2","atla","xe-0/1/3"), #05638
                  ("seat","xe-0/0/0","salt","xe-0/1/1"), #05565
                  ("chic","xe-1/0/2","kans","xe-0/0/3"), #05781
                  ("hous","xe-1/1/0","kans","xe-1/0/0"), #05560
                  ("seat","xe-0/1/0","losa","xe-0/0/0"), #05564
                  ("salt","xe-0/0/1","losa","xe-0/1/3"), #05571
                  ("seat","xe-1/0/0","salt","xe-0/1/3"), #05573
                  ("newy32aoa","et-3/0/0-0","wash","et-3/0/0-0"), #06126
                  ("newy32aoa","et-3/0/0-1","wash","et-3/0/0-1"), #06126-2
                  ("chic","xe-1/1/1","atla","xe-0/0/0"), #05419
                  ("losa","xe-0/1/0","seat","xe-2/1/0"), #05572
                  ("hous","xe-0/1/0","losa","ge-6/1/0"), #05581
                  ("atla","xe-0/0/3","wash","xe-1/1/3"), #05251
                  ("hous","xe-3/1/0","kans","ge-6/2/0"), #05561
                  ("atla","ge-6/0/0","hous","xe-0/0/0"), #05423
                  ("chic","xe-1/0/3","kans","xe-1/0/3"), #05976
                  ("losa","xe-0/0/3","salt","xe-0/1/0"), #05563
                  ("atla","ge-6/1/0","hous","xe-1/0/0"), #05562
                  ("atla","xe-1/0/3","wash","xe-0/0/0"), #06366
                  ("chic","xe-2/1/3","wash","xe-0/1/3"), #05637
                  ("atla","xe-1/0/1","wash","xe-0/0/3"), #05133
                  ("kans","xe-0/1/1","salt","ge-6/0/0"), #05566
                  ("chic","xe-1/1/0","newy32aoa","xe-0/0/0"), #05239
              ]

    def __init__(self):
        super(Internet2Topo, self).__init__(Internet2Topo.Definition,
                                            load_internet2_backbone_ntf,
                                            load_internet2_backbone_ttf,
                                            load_internet2_backbone_port_to_id_map,
                                            juniperRouter)

class StanfordTopo(TfTopology):
    Definition = [("bbra_rtr","te7/3","goza_rtr","te2/1"),
                  ("bbra_rtr","te7/3","pozb_rtr","te3/1"),
                  ("bbra_rtr","te1/3","bozb_rtr","te3/1"),
                  ("bbra_rtr","te1/3","yozb_rtr","te2/1"),
                  ("bbra_rtr","te1/3","roza_rtr","te2/1"),
                  ("bbra_rtr","te1/4","boza_rtr","te2/1"),
                  ("bbra_rtr","te1/4","rozb_rtr","te3/1"),
                  ("bbra_rtr","te6/1","gozb_rtr","te3/1"),
                  ("bbra_rtr","te6/1","cozb_rtr","te3/1"),
                  ("bbra_rtr","te6/1","poza_rtr","te2/1"),
                  ("bbra_rtr","te6/1","soza_rtr","te2/1"),
                  ("bbra_rtr","te7/2","coza_rtr","te2/1"),
                  ("bbra_rtr","te7/2","sozb_rtr","te3/1"),
                  ("bbra_rtr","te6/3","yoza_rtr","te1/3"),
                  ("bbra_rtr","te7/1","bbrb_rtr","te7/1"),
                  ("bbrb_rtr","te7/4","yoza_rtr","te7/1"),
                  ("bbrb_rtr","te1/1","goza_rtr","te3/1"),
                  ("bbrb_rtr","te1/1","pozb_rtr","te2/1"),
                  ("bbrb_rtr","te6/3","bozb_rtr","te2/1"),
                  ("bbrb_rtr","te6/3","roza_rtr","te3/1"),
                  ("bbrb_rtr","te6/3","yozb_rtr","te1/1"),
                  ("bbrb_rtr","te1/3","boza_rtr","te3/1"),
                  ("bbrb_rtr","te1/3","rozb_rtr","te2/1"),
                  ("bbrb_rtr","te7/2","gozb_rtr","te2/1"),
                  ("bbrb_rtr","te7/2","cozb_rtr","te2/1"),
                  ("bbrb_rtr","te7/2","poza_rtr","te3/1"),
                  ("bbrb_rtr","te7/2","soza_rtr","te3/1"),
                  ("bbrb_rtr","te6/1","coza_rtr","te3/1"),
                  ("bbrb_rtr","te6/1","sozb_rtr","te2/1"),
                  ("boza_rtr","te2/3","bozb_rtr","te2/3"),
                  ("coza_rtr","te2/3","cozb_rtr","te2/3"),
                  ("goza_rtr","te2/3","gozb_rtr","te2/3"),
                  ("poza_rtr","te2/3","pozb_rtr","te2/3"),
                  ("roza_rtr","te2/3","rozb_rtr","te2/3"),
                  ("soza_rtr","te2/3","sozb_rtr","te2/3"),
                  ("yoza_rtr","te1/1","yozb_rtr","te1/3"),
                  ("yoza_rtr","te1/2","yozb_rtr","te1/2"),
              ]

    def __init__(self):
        super(StanfordTopo, self).__init__(StanfordTopo.Definition,
                                           load_stanford_backbone_ntf,
                                           load_stanford_backbone_ttf,
                                           load_stanford_backbone_port_to_id_map,
                                           ciscoRouter)

class DiamondTopo(Topology):
    def __init__(self):
        super(DiamondTopo, self).__init__()
        g = networkx.Graph()
        g.add_nodes_from(['s1', 's2', 's3', 's4'])
        g.add_edges_from([('s1','s2'),
                          ('s1','s3'),
                          ('s2','s4'),
                          ('s3','s4')])

        self.build_from_graph(g)

class DiamondExtendedTopo(Topology):
    def __init__(self):
        super(DiamondExtendedTopo, self).__init__()
        g = networkx.Graph()
        g.add_nodes_from(['s1', 's2', 's3', 's4', 's5', 's6'])
        g.add_edges_from([('s1','s2'),
                          ('s2','s3'),
                          ('s3','s5'),
                          ('s2','s4'),
                          ('s4','s5'),
                          ('s5','s6')])

        self.build_from_graph(g)

class DoubleDiamondTopo(Topology):
    def __init__(self):
        super(DoubleDiamondTopo, self).__init__()
        g = networkx.Graph()
        g.add_edges_from([('s1', 's2'),
                          ('s2', 's3'),
                          ('s2', 's4'),
                          ('s4', 's5'),
                          ('s5', 's6'),
                          ('s6', 's8'),
                          ('s8', 's10'),
                          ('s3', 's5'),
                          ('s5', 's7'),
                          ('s7', 's9'),
                          ('s9', 's10')])

        self.build_from_graph(g)

class DiamondClusterTopo(Topology):
    def __init__(self):
        super(DiamondClusterTopo, self).__init__()
        g = networkx.Graph()
        g.add_edges_from([('Src', 's0'),
                          ('s0', 's1'),
                          ('s1', 's2'),
                          ('s2', 's3'),
                          ('s3', 's4'),
                          ('s4', 'Fw1'),
                          ('Fw1', 's5'),
                          ('s5', 's6'),
                          ('s6', 'Dst'),
                          ('Src', 's7'),
                          ('s7', 's8'),
                          ('s8', 's9'),
                          ('s9', 'Fw2'),
                          ('Fw2', 's10'),
                          ('s10', 's11'),
                          ('s11', 's12'),
                          ('s12', 's13'),
                          ('s13', 'Dst'),
                          ('Src', 's14'),
                          ('s14', 'Core'),
                          ('Core', 's15'),
                          ('s15', 'Dst'),
                          ('s14', 's16'),
                          ('s16', 'Core'),
                          ('s16', 'Fw1'),
                          ('s18', 'Fw1'),
                          ('s18', 'Core'),
                          ('s18', 's15'),
                          ('s14', 's17'),
                          ('s17', 'Core'),
                          ('s17', 'Fw2'),
                          ('s19', 'Fw2'),
                          ('s19', 'Core'),
                          ('s19', 's15'),
                          ('Core', 'Fw1'),
                          ('Core', 'Fw2')])

        self.build_from_graph(g)

class ThintreeTopo(Topology):
    def __init__(self):
        super(ThintreeTopo, self).__init__()
        g = networkx.Graph()
        g.add_nodes_from(['s1', 's2', 's3', 's4', 's5', 's6',
                          's7', 's8', 's9', 's10', 's11'])
        g.add_edges_from([('s1','s2'),
                          ('s1','s3'),
                          ('s2','s4'),
                          ('s2','s5'),
                          ('s2','s6'),
                          ('s2','s7'),
                          ('s3','s4'),
                          ('s3','s5'),
                          ('s3','s6'),
                          ('s3','s7'),
                          ('s8','s4'),
                          ('s8','s5'),
                          ('s8','s6'),
                          ('s8','s7'),
                          ('s9','s4'),
                          ('s9','s5'),
                          ('s9','s6'),
                          ('s9','s7'),
                          ('s8','s10'),
                          ('s9','s10'),
                          ('s8','s11'),
                          ('s9','s11')])

        self.build_from_graph(g)

class FattreeTopo(Topology):
    def __init__(self, k=4, density=1):
        super(FattreeTopo, self).__init__()
        self.size = k
        self.pods = {}
        self.pods_rev = {}
        self._make_topo()

    @classmethod
    def make_connections(cls, instance, density):
        # f = math.factorial
        # n = len(instance.hosts.keys())
        # r = 2
        # combinations = f(n) / (f(r) * f(n-r))
        # count = int(density * combinations)
        # pairs = list(itertools.combinations(instance.hosts.keys(), 2))
        # for p in random.sample(pairs, count):
        #     print p[0], p[1]
        #     instance.add_path(p[0], p[1])
        count = int(density * len(instance.hosts.keys()))
        for p,v in pairwise(random.sample(instance.hosts.keys(), count)):
            logger.debug("Creating connection (src, dst) = (%s, %s)", p, v)
            instance.add_path(p,v)

    def _make_topo(self):
        self.graph = self._generate_graph()
        switches = [node for node in self.graph.nodes() if node[0] == 's']
        hosts = [node for node in self.graph.nodes() if node[0] == 'h']

        startip = ip2int("10.1.0.0")
        for name in switches:
            ip = startip + len(self.switches) + 1
            self.switches[name] = Switch(name=name,
                                         ip=int2ip(ip))

        count = 0
        for name in hosts:
            podnum, idx = self.pods_rev[name]
            ip = "10.0.{0}.{1}".format(podnum, idx)
            mac = int2mac(count)
            count += 1
            self.hosts[name] = Host(name=name, ip=ip, mac=mac)

        for e0, e1 in self.graph.edges():
            if e0 not in self.edges:
                self.edges[e0] = []
            if e1 not in self.edges:
                self.edges[e1] = []

            self.edges[e0].append(e1)
            self.edges[e1].append(e0)

    def _generate_graph(self):
        cores = (self.size/2)**2
        aggs = (self.size/2) * self.size
        edges = (self.size/2) * self.size
        hosts = (self.size/2)**2 * self.size

        g = networkx.Graph()
        for pod in range(0, self.size):
            agg_offset = cores + self.size/2 * pod
            edge_offset = cores + aggs + self.size/2 * pod
            host_offset = cores + aggs + edges + (self.size/2)**2 * pod

            for agg in range(0, self.size/2):
                core_offset = agg * self.size/2

                # connect core and aggregate switches
                for core in range(0, self.size/2):
                    aggname = "s{0}".format(agg_offset + agg)
                    corename = "s{0}".format(core_offset + core)
                    g.add_edge(aggname, corename)

                # connect aggregate and edge switches
                for edge in range(0, self.size/2):
                    aggname = "s{0}".format(agg_offset + agg)
                    edgename = "s{0}".format(edge_offset + edge)
                    g.add_edge(aggname, edgename)
                    self._egresses.append(edgename)

            # connect edge switches with hosts
            for edge in range(0, self.size/2):
                for h in range(0, self.size/2):
                    edgename = "s{0}".format(edge_offset + edge)
                    hostname = "h{0}".format(host_offset + self.size/2 * edge + h)
                    g.add_edge(edgename, hostname)

                    if pod not in self.pods:
                        self.pods[pod] = []

                    self.pods[pod].append(hostname)
                    self.pods_rev[hostname] = (pod, len(self.pods[pod]))

        return g

class SosrTopo(Topology):
    def __init__(self):
        super(SosrTopo, self).__init__()
        g = networkx.Graph()
        g.add_nodes_from(['A', 'B', 'C', 'F1', 'F2', 'X', 'Y', 'Z'])
        g.add_edges_from([('A', 'F1'),
                          ('A', 'F2'),
                          ('B', 'F1'),
                          ('B', 'F2'),
                          ('C', 'F1'),
                          ('C', 'F2'),
                          ('F1', 'X'),
                          ('F2', 'Y'),
                          ('Y', 'Z'),
                          ('X', 'Z')])

        self.build_from_graph(g)

class RocketfuelTopo(Topology):
    dataset_path = "rocketfuel_maps"

    def __init__(self, asnum=1755):
        super(RocketfuelTopo, self).__init__()
        fname = os.path.join(RocketfuelTopo.dataset_path,
                             "{0}.cch".format(asnum))
        if not os.path.isfile(fname):
            raise Exception("Invalid AS number: {0} does not exist"
                            .format(fname))

        topo = fnss.parse_rocketfuel_isp_map(fname)

        # TODO: support directed topologies
        renames = {}
        for node in sorted(topo.nodes()):
            renames[node] = "s{0}".format(len(renames))

        if topo.is_directed():
            g = networkx.DiGraph()
        else:
            g = networkx.Graph()

        for m, n in topo.edges():
            g.add_edge(renames[m], renames[n])

        self.build_from_graph(g)

    @classmethod
    def ASes(cls):
        return [os.path.splitext(cch)[0] for cch in
                os.listdir(RocketfuelTopo.dataset_path)
                if cch[0].isdigit() and os.path.splitext(cch)[1] == '.cch']

def mp_parse_switch((topo, fname)):
    return topo.parse_switch_file(fname)

class As1755Topo(Topology):
    def __init__(self, mp=True, mp_procs=12, no_ft=False, path="../data_set/RocketFuel/AS-1755"):
        super(As1755Topo, self).__init__()
        if not no_ft:
            self.read_flowtable(path, mp, mp_procs)
        self.read_links(path)
        self.build_from_graph(self.graph)

        # for sw in self.switches.keys():
        #     if not sw.startswith("10."):
        #         self._egresses.append(sw)

    def read_links(self, path):
        topofile = os.path.join(path, "as1755.topo")
        #self.graph = networkx.DiGraph()
        self.graph = networkx.Graph()

        with open(topofile) as f:
            for line in f.readlines():
                tokens = line.split()
                if len(tokens) != 2:
                    raise Exception("Invalid line in topo: {0}".format(line))

                # skip duplicates and self loops
                if not self.graph.has_edge(tokens[0], tokens[1]) and \
                   tokens[0] != tokens[1]:
                    self.graph.add_edge(tokens[0], tokens[1])

    def read_flowtable(self, path, mp, mp_procs):
        files = [os.path.join(path, f) for f in os.listdir(path)
                 if os.path.isfile(os.path.join(path, f))
                 and f[0] == 'R']

        if mp:
            import time
            pool = multiprocessing.Pool(processes=mp_procs)
            args = [(self, fname) for fname in files]
            for sw, ft in pool.imap(mp_parse_switch, args):
                self.switches[sw] = Switch(name=sw, ip=sw)
                self.switches[sw].ft = ft
            pool.close()
        else:
            for fname in files:
                for sw, ft in self._parse_switch_file(fname):
                    self.switches[sw] = Switch(name=sw, ip=sw)
                    self.switches[sw].ft = ft

    def parse_switch_file(self, fname):
        switch = os.path.basename(fname)[1:]
        logger.debug("Parsing rules in switch {0}".format(switch))
        rules = []
        with open(fname) as f:
            for line in f.readlines():
                tokens = line.split()
                dst = tokens[2]
                wc = tokens[3]
                nexthop = tokens[5]
                priority = int(tokens[7])

                if '/' in dst:
                    dst_tokens = dst.split('/')
                    block = int(dst_tokens[1])
                    dst = dst_tokens[0]

                    if wc2ip(32-block) != wc:
                        raise Exception("Error: inconsistency in wildcard")

                if tokens[4] != switch:
                    raise Exception("Location != switch name")

                r = trie.Rule()
                r.ruleType = trie.Rule.FORWARDING
                r.fieldValue[HeaderField.Index["NW_DST"]] = ip2int(dst)
                r.fieldMask[HeaderField.Index["NW_DST"]] = ip2int(wc)
                r.priority = priority
                r.nextHop = nexthop
                r.location = switch
                rules.append(r)

        return (switch, rules)

    @classmethod
    def write_topo(cls, class_file_path, dest="as1755.topo"):
        files = [os.path.join(class_file_path, f) for f in
                 os.listdir(class_file_path)]

        links = {}
        for fname in files:
            with open(fname) as f:
                for line in f.readlines():
                    tokens = line.split()
                    if tokens[1] == tokens[2]:
                        continue

                    if tokens[1] not in links:
                        links[tokens[1]] = []

                    if tokens[2] not in links[tokens[1]]:
                        links[tokens[1]].append(tokens[2])

        s = []
        for src, dsts in links.iteritems():
            for dst in dsts:
                s += "{0} {1}\n".format(src, dst)

        with open(dest, 'w') as f:
            f.writelines(s)
