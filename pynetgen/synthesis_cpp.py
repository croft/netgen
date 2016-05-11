#!/usr/bin/env python

import time
import synthesis
from network import NetworkConfig
from grammar import SpecGrammar
from spec import Specification
from solver import AbstractNetwork, Solver
from topos import DiamondTopo

def conv_abstract_network(net):
    nodes = net.nodes
    sources = net.sources
    egresses = net.sinks
    immutables = net.immutables

    topo = []
    for m, n in net.concrete_network.iteredges():
        topo.append((net.node_intrep[m], net.node_intrep[n]))

    classes = []
    for pcid, pc in net.class_pcrep.iteritems():
        for m, n in pc.iteredges():
            classes.append((net.node_intrep[m], pcid, net.node_intrep[n]))

    fsa = []
    for s1, t, s2 in net.fsa.transitions:
        s1 = int(s1)
        s2 = int(s2)
        if t in net.node_intrep:
            fsa.append((s1, net.node_intrep[t], s2))
        else:
            fsa.append((s1, int(t), s2))

    symbols = net.fsa.symbolAliases.values()
    states = [int(s) for s in net.fsa.states]
    finals = [int(s) for s in net.fsa.final]
    initial = int(net.fsa.initial)
    dead = 0

    return AbstractNetwork(nodes,
                           sources,
                           egresses,
                           immutables,
                           topo,
                           classes,
                           fsa,
                           states,
                           symbols,
                           finals,
                           initial,
                           dead)

def diamond_test():
    config = NetworkConfig(paths=[('s1', 's4', ['s1', 's2', 's4'])],
                           egresses=['s4'])
    topo = DiamondTopo()
    topo.apply_config(config)

    specstr = "not match(ip_src=a.b.c.d); s1: .* s2 .* => (N-s2) s3 (N-s2)"
    s = Specification.parseString(topo, specstr)
    net = synthesis.AbstractNetwork(topo, s)
    abs_net = conv_abstract_network(net)
    slvr = Solver(abs_net)

    t = time.time()
    result = slvr.solve()
    t = time.time() - t

    expected = [('s3', 's4'), ('s1', 's3')]
    expected = [(net.node_intrep[s], net.node_intrep[d]) for (s,d) in expected]
    print "Result:", result
    print "Expect:", expected
    print "Solver time: {0}ms".format(round(t * 1000, 3))

def dummy_test():
    a = AbstractNetwork([1,2,3],
                        [2,3,4],
                        [4,5,6],
                        [1,2],
                        [(1,2), (2,3)],
                        [],
                        [],
                        [],
                        [],
                        [],
                        1,
                        0)

    s = Solver(a)
    res = s.solve()
    print "result", res

if __name__ == "__main__":
    #dummy_test()
    diamond_test()
