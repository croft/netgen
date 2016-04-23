#!/usr/bin/env python

import igraph
import itertools
import math
import random
import socket
import struct
from netaddr import EUI

import dijkstra

def ip2int(addr):
    return struct.unpack("!I", socket.inet_aton(addr))[0]

def int2ip(addr):
    return socket.inet_ntoa(struct.pack("!I", addr))

def mac2int(addr):
    mac = EUI(addr.replace("-", ":"))
    return int(mac)

def int2mac(addr):
    h = "{0:#0{1}x}".format(addr, 12)[2:]
    return ':'.join(s.encode('hex') for s in h.decode('hex'))

def generate_ip(idx):
    ipbase = ip2int("10.0.0.1")
    return int2ip(ipbase + idx)

def generate_mac(idx):
    macbase = mac2int("00:00:00:00:00:01")
    return int2mac(macbase + idx)

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = itertools.tee(iterable)
    next(b, None)
    return itertools.izip(a, b)

class Node(object):
    def __init__(self, ip=None, mac=None, name=None):
        self.ip = ip
        self.mac = mac
        self.name = name

class Topology(object):
    def __init__(self):
        self.switches = {}
        self.hosts = {}
        self.edges = {}
        self.paths = {}

    def make_topofile(self, dest):
        out = []
        for src, dsts in self.edges.iteritems():
            for d in dsts:
                out.append("{0} {1}\n".format(src, d))

        print len(out)
        # with open(os.path.join(dest, "topo.txt"), 'w') as f:
        #     f.writelines(out)

class FattreeTopo(Topology):
    def __init__(self, k):
        super(FattreeTopo, self).__init__()
        self.size = k
        self.host_agg = {}
        self.host_edge = {}
        self.edge_types = {}
        self.distances = {}
        self._make_topo()
        # self._make_hints()

    def make_connections(self, density):
        f = math.factorial
        n = len(self.hosts.keys())
        r = 2
        combinations = f(n) / (f(r) * f(n-r))
        count = int(density * combinations)
        pairs = list(itertools.combinations(self.hosts.keys(), 2))
        for p in random.sample(pairs, count):
            self.path(p[0], p[1])

    def add_path(self, src, dst, path):
        if src not in self.paths.keys():
            self.paths[src] = {}

        self.paths[src][dst] = path

        # assume paths are bidirectional
        if dst not in self.paths.keys():
            self.paths[dst] = {}
            
        self.paths[dst][src] = path
       
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
            self.switches[name] = Node(generate_ip(i), generate_mac(i), name)

        for i in range(switches, switches + (self.size/2)**2 * self.size):
            name = "h%d" % i
            nodes[i] = name
            self.hosts[name] = Node(generate_ip(i), generate_mac(i), name)
            self.host_edge[name] = None
            self.host_agg[name] = []

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

        return g

f = FattreeTopo(4)
f.make_connections(0.1)

# print f.path("h30", "h31")
# print f.path("h32", "h35")
# print f.path("h26", "h31")
# print f.alt_path("h26", "h31")
