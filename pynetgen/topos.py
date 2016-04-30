#!/usr/bin/env python

import igraph
import itertools
import math
import random

from utils.load_stanford_backbone import *
from utils.load_internet2_backbone import *
from headerspace.applications import *
from headerspace.hs import *
from headerspace.tf import *
from config_parser.cisco_router_parser import ciscoRouter
from config_parser.juniper_parser import juniperRouter
from config_parser.transfer_function_to_openflow import OpenFlow_Rule_Generator

import dijkstra
from network import Topology, Switch, Host, FlowEntry, int2mac

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = itertools.tee(iterable)
    next(b, None)
    return itertools.izip(a, b)

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
        self._make_topo()
        self.paths = {}
        #self.add_path('h1', 'h2', ['h1', 's0', 's1', 's3', 'h2'])
        self.add_path('s0', 's3', ['s0', 's1', 's3'])
        self.make_flowtable()

        # TODO: manually set egress
        self.egress.append('s3')

    def make_flowtable(self):
        # make forwarding tables
        for src in self.paths.keys():
            for dst in self.paths[src].keys():
                path = self.paths[src][dst]
                src_ip = self.nodes[src].ip
                dst_ip = self.nodes[dst].ip
                wc = "255.255.255.255"
                #for location, nexthop in pairwise(path[1:]):
                for location, nexthop in pairwise(path):
                    flow = FlowEntry(dest=dst_ip,
                                     wildcard=wc,
                                     location=location,
                                     nexthops=nexthop,
                                     src=src_ip)
                    self.switches[location].ft.append(flow)

    def add_path(self, src, dst, path):
        if src not in self.paths.keys():
            self.paths[src] = {}

        self.paths[src][dst] = path

        # assume paths are bidirectional
        # if dst not in self.paths.keys():
        #     self.paths[dst] = {}
        # self.paths[dst][src] = path

    def _make_topo(self):
        g = igraph.Graph()
        #g.add_vertices(['s0', 's1', 's2', 's3', 'h1', 'h2'])
        g.add_vertices(['s0', 's1', 's2', 's3'])
        g.add_edges([('s0','s1'),
                     ('s0','s2'),
                     ('s1','s3'),
                     ('s2','s3')])
#                     ('h1', 's0'),
#                     ('h2', 's3')])

        nodes = []
        for name in ['s0', 's1', 's2', 's3']:
            nodes.append(name)
            ip = "10.0.1.{0}".format(len(self.switches.keys()) + 1)
            self.switches[name] = Switch(name=name ,ip=ip)

        # for name in ['h1', 'h2']:
        #     nodes.append(name)
        #     ip = "10.0.0.{0}".format(len(self.hosts.keys()) + 1)
        #     self.hosts[name] = Host(name=name, ip=ip)

        edges = g.get_edgelist()
        for e in edges:
            e0 = g.vs[e[0]].attributes()['name']
            e1 = g.vs[e[1]].attributes()['name']

            if e0 not in self.edges:
                self.edges[e0] = []

            if e1 not in self.edges:
                self.edges[e1] = []

            self.edges[e0].append(e1)
            self.edges[e1].append(e0)

class FattreeTopo(Topology):
    def __init__(self, k, path_density):
        super(FattreeTopo, self).__init__()
        self.size = k
        self.path_density = path_density
        self.distances = {}
        self.pods = {}
        self.pods_rev = {}
        self.paths = {}

        self._make_topo()
        self.make_connections(self.path_density)
        self.make_flowtable()

    def make_flowtable(self):
        # make forwarding tables
        for src in self.paths.keys():
            for dst in self.paths[src].keys():
                path = self.paths[src][dst]
                src_ip = self.nodes[src].ip
                dst_ip = self.nodes[dst].ip
                wc = "255.255.255.255"
                for location, nexthop in pairwise(path[1:]):
                    flow = FlowEntry(dest=dst_ip,
                                     wildcard=wc,
                                     location=location,
                                     nexthops=nexthop,
                                     src=src_ip)
                    self.switches[location].ft.append(flow)

    def make_connections(self, density):
        # f = math.factorial
        # n = len(self.hosts.keys())
        # r = 2
        # combinations = f(n) / (f(r) * f(n-r))
        # count = int(density * combinations)
        # pairs = list(itertools.combinations(self.hosts.keys(), 2))
        # for p in random.sample(pairs, count):
        #     print p[0], p[1]
        #     self.path(p[0], p[1])
        count = int(density * len(self.hosts.keys()))
        for p,v in pairwise(random.sample(self.hosts.keys(), count)):
            print p,v
            self.path(p,v)

    def add_path(self, src, dst, path):
        if src not in self.paths.keys():
            self.paths[src] = {}

        self.paths[src][dst] = path

        # assume paths are bidirectional
        # if dst not in self.paths.keys():
        #     self.paths[dst] = {}
        # self.paths[dst][src] = path

    def path(self, src, dst):
        path = dijkstra.shortestPath(self.distances, src, dst)
        self.add_path(src, dst, path)
        return path

    def alt_path(self, src, dst):
        distances = self.distances.copy()
        for k,v in pairwise(self.paths[src][dst]):
            distances[k][v] = distances[k][v] + 1

        path = dijkstra.shortestPath(self.distances, src, dst)
        self.add_path(src, dst, path)
        return path

    def _make_topo(self):
        g = self._generate_graph()
        edges = g.get_edgelist()

        switches = (self.size/2)**2 + self.size * self.size
        nodes = {}
        for i in range(switches):
            name = "s%d" % i
            nodes[i] = name
            self.switches[name] = Switch(name=name)

        for i in range(switches, switches + (self.size/2)**2 * self.size):
            name = "h%d" % i
            nodes[i] = name
            self.hosts[name] = Host(name=name)

        for e in edges:
            e0 = nodes[e[0]]
            e1 = nodes[e[1]]

            if e0 not in self.edges:
                self.edges[e0] = []

            if e1 not in self.edges:
                self.edges[e1] = []

            self.edges[e0].append(e1)
            self.edges[e1].append(e0)

            if e0 not in self.distances.keys():
                self.distances[e0] = {}

            self.distances[e0][e1] = 2

            if e1 not in self.distances.keys():
                self.distances[e1] = {}

            self.distances[e1][e0] = 2

        count = 1
        for h in self.hosts:
            podnum, idx = self.pods_rev[h]
            self.hosts[h].ip = "10.0.{0}.{1}".format(podnum, idx)
            self.hosts[h].mac = int2mac(count)
            count += 1

    def _generate_graph(self):
        cores = (self.size/2)**2
        aggs = (self.size/2) * self.size
        edges = (self.size/2) * self.size
        hosts = (self.size/2)**2 * self.size

        g = igraph.Graph()
        g.add_vertices(cores + aggs + edges + hosts)
        g.vs['type'] = ['core'] * cores + ['agg'] * aggs + ['edge'] * edges + \
                       ['hosts'] * hosts

        for pod in range(0, self.size):
            agg_offset = cores + self.size/2 * pod
            edge_offset = cores + aggs + self.size/2 * pod
            host_offset = cores + aggs + edges + (self.size/2)**2 * pod

            for agg in range(0, self.size/2):
                core_offset = agg * self.size/2

                # connect core and aggregate switches
                for core in range(0, self.size/2):
                    g.add_edge(agg_offset + agg, core_offset + core)

                # connect aggregate and edge switches
                for edge in range(0, self.size/2):
                    g.add_edge(agg_offset + agg, edge_offset + edge)

            # connect edge switches with hosts
            for edge in range(0, self.size/2):
                for h in range(0, self.size/2):
                    g.add_edge(edge_offset + edge,
                               host_offset + self.size/2 * edge + h)

                    if pod not in self.pods:
                        self.pods[pod] = []

                    hnum = host_offset + self.size/2 * edge + h
                    self.pods[pod].append("h%d"%hnum)
                    self.pods_rev["h%d"%hnum] = (pod, len(self.pods[pod]))

        return g