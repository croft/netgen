#!/usr/bin/env python

import fnss
import math
import networkx
import os
import random

from utils.load_stanford_backbone import *
from utils.load_internet2_backbone import *
from headerspace.applications import *
from headerspace.hs import *
from headerspace.tf import *
from config_parser.cisco_router_parser import ciscoRouter
from config_parser.juniper_parser import juniperRouter
from config_parser.transfer_function_to_openflow import OpenFlow_Rule_Generator

from fields import int2mac, ip2int, int2ip
from log import logger
from network import Topology, Switch, Host, FlowEntry, pairwise

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

        for tf in self.ntf.tf_list:
            ofg = OpenFlow_Rule_Generator( tf, self.router.HS_FORMAT())
            rules = ofg.generate_of_rules()
            swname = tf.prefix_id

            for rule in rules:
                dest = int2ip(rule['ip_dst_match'])
                wc = wc2ip(rule['ip_dst_wc'])
                outports = rule['out_ports']
                location = tf.prefix_id
                nexthops = []

                for port in outports:
                    if port in self.edge_ports:
                        # TODO
                        pass
                    else:
                        p = str(port - self.router.PORT_TYPE_MULTIPLIER)
                        if p in self.port_reverse_map.keys():
                            portname = self.port_reverse_map[p].split("-")[1]
                            if portname in self.intfs[location].keys():
                                nexthop = self.intfs[location][portname]
                                nexthops.append(nexthop)
                            else:
                                # TODO
                                pass

                flow = FlowEntry(dest=dest,
                                 wildcard=wc,
                                 location=location,
                                 nexthops=nexthops)

                if len(nexthops) > 0:
                    self.switches[swname].ft.append(flow)

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
        self._make_topo()
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
    def __init__(self, asnum=1755):
        super(RocketfuelTopo, self).__init__()
        fname = os.path.join("rocketfuel_maps", "{0}.cch".format(asnum))
        if not os.path.isfile(fname):
            raise Exception("Invalid AS number: {0} does not exist"
                            .format(fname))

        topo = fnss.parse_rocketfuel_isp_map(fname)

        # TODO: support directed topologies
        renames = {}
        for node in sorted(topo.nodes()):
            renames[node] = "s{0}".format(len(renames))

        g = networkx.Graph()
        for m, n in topo.edges():
            g.add_edge(renames[m], renames[n])

        self.build_from_graph(g)
