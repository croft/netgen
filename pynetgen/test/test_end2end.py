#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from grammar import SpecGrammar
from network import NetworkConfig
from topos import DiamondTopo, DiamondExtendedTopo, ThintreeTopo, FattreeTopo
from spec import Specification
from synthesis import Synthesizer

def runSynthesis(topo, config, spec, expected):
    topo.apply_config(config)
    s = Specification.parseString(topo, spec)
    solver = Synthesizer(topo, s)
    result = solver.solve()
    for edge in expected:
        assert edge in result

class testFattree(unittest.TestCase):

    def testSameCore(self):
        # different cores, different aggregates
        config = NetworkConfig(paths=[('h25', 'h34', None)])
        spec = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s1 (N-s0)* od"
        expected = [('s6', 's1'), ('s1', 's10')]
        runSynthesis(FattreeTopo(), config, spec, expected)

    def testDifferentCore(self):
        # different cores, different aggregates
        config = NetworkConfig(paths=[('h25', 'h34', None)])
        spec = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s3 (N-s0)* od"
        expected = [('s14', 's7'), ('s7', 's3'), ('s11', 's19'), ('s3', 's11')]
        runSynthesis(FattreeTopo(), config, spec, expected)

    def testImmutable(self):
        # different aggregate, but make core immutable
        # note: difference is core s2 and s3 between two tests
        config = NetworkConfig(paths=[('h25', 'h34', None)])
        spec = "not match(ip_src=a.b.c.d); s14: .* s10 .* => (N-s10)* s11 (N-s10)* od NM:{s2}"
        expected = [('s7', 's3'), ('s14', 's7'), ('s3', 's11'), ('s11', 's19')]
        runSynthesis(FattreeTopo(), config, spec, expected)

        config = NetworkConfig(paths=[('h25', 'h34', None)])
        spec = "not match(ip_src=a.b.c.d); s14: .* s10 .* => (N-s10)* s11 (N-s10)* od NM:{s3}"
        expected = [('s7', 's2'), ('s14', 's7'), ('s11', 's19'), ('s2', 's11')]
        runSynthesis(FattreeTopo(), config, spec, expected)

class testDiamond(unittest.TestCase):

    def testForwardPath(self):
        config = NetworkConfig(paths=[('s1', 's4', ['s1', 's2', 's4'])],
                               egresses=['s4'])
        spec = "not match(ip_src=a.b.c.d); s1: .* s2 .* => (N-s2) s3 (N-s2)"
        expected = [('s3', 's4'), ('s1', 's3')]
        runSynthesis(DiamondTopo(), config, spec, expected)

    def testReversePath(self):
        config = NetworkConfig(paths=[('s4', 's1', ['s4', 's2', 's1'])],
                               egresses=['s1'])
        spec = "not match(ip_src=a.b.c.d); s4: .* s2 .* => (N-s2) s3 (N-s2)"
        expected = [('s4', 's3'), ('s3', 's1')]
        runSynthesis(DiamondTopo(), config, spec, expected)
