#!/usr/bin/env python

import unittest

import os
from runner import addPath
addPath()

from grammar import SpecGrammar
from network import NetworkConfig
from spec import Specification
from synthesis import Synthesizer
from topos import (DiamondTopo, DiamondExtendedTopo,
                   ThintreeTopo, FattreeTopo, SosrTopo,
                   DiamondClusterTopo, As1755Topo)

cwd = os.path.dirname(os.path.realpath(__file__))

import synthesis
#Synthesizer = synthesis.CppSynthesizer
#Synthesizer = synthesis.CppCachingSynthesizer
Synthesizer = synthesis.PythonSynthesizer
#Synthesizer = synthesis.PythonCachingSynthesizer

def runSynthesisConfigured(topo, spec, expected):
    s = Specification.parseString(topo, spec)
    solver = Synthesizer(topo, s)
    result = solver.solve()
    for edge in expected:
        assert edge in result

def runSynthesis(topo, config, spec, expected):
    topo.apply_config(config)
    runSynthesisConfigured(topo, spec, expected)

class testAs1755(unittest.TestCase):
    def test_1K_1PC(self):
        as1755dir = os.path.join(cwd, "../../data_set/RocketFuel/AS-1755")
        classdir = os.path.join(cwd, "rf_classes")
        topo = As1755Topo(no_ft=True, path=as1755dir)
        topo.deserialize_classes(classdir, limit=1)

        spec = "not match(ip_src=a.b.c.d); 10.0.0.166: .* 10.0.0.150  .* => .* 10.0.0.154 .* od"
        expected = [('10.0.0.166', '10.0.0.154')]
        runSynthesisConfigured(topo, spec, expected)

        spec = "not match(ip_src=a.b.c.d); 10.0.3.18: .* 10.0.2.241  .* =>  10.0.3.18 (N-10.0.2.241) .* od"
        expected = [('10.0.3.18', '10.0.2.242')]
        runSynthesisConfigured(topo, spec, expected)

        spec = "not match(ip_src=a.b.c.d); 10.0.4.70: .* 10.0.0.122  .* => (N-10.0.0.122)* od"
        expected = [('10.0.3.102', '10.0.3.222')]
        runSynthesisConfigured(topo, spec, expected)

    def test_2K_1PC(self):
        as1755dir = os.path.join(cwd, "../../data_set/RocketFuel/AS-1755")
        classdir = os.path.join(cwd, "rf_classes")
        topo = As1755Topo(no_ft=True, path=as1755dir)
        topo.deserialize_classes(classdir, limit=1)

        spec = "not match(ip_src=a.b.c.d); 10.0.1.162: .* 10.0.1.153  .* => (N-10.0.1.153)* od"
        expected = [('10.0.1.162', '10.0.2.174'), ('10.0.2.174', '10.0.1.134')]
        runSynthesisConfigured(topo, spec, expected)

class testFattree(unittest.TestCase):
    config = NetworkConfig(paths=[('h25', 'h34',  ['h25', 's14', 's6', 's0',
                                                   's10', 's19', 'h34'])])

    def testSameCore(self):
        # different cores, different aggregates
        spec = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s1 (N-s0)* od"
        expected = [('s6', 's1'), ('s1', 's10')]
        runSynthesis(FattreeTopo(), testFattree.config, spec, expected)

    def testDifferentCore(self):
        # different cores, different aggregates
        spec = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s3 (N-s0)* od"
        expected = [('s14', 's7'), ('s7', 's3'), ('s11', 's19'), ('s3', 's11')]
        runSynthesis(FattreeTopo(), testFattree.config, spec, expected)

    def testImmutable(self):
        # different aggregate, but make core immutable
        # note: difference is core s2 and s3 between two tests
        spec = "not match(ip_src=a.b.c.d); s14: .* s10 .* => (N-s10)* s11 (N-s10)* od NM:{s2}"
        expected = [('s7', 's3'), ('s14', 's7'), ('s3', 's11'), ('s11', 's19')]
        runSynthesis(FattreeTopo(), testFattree.config, spec, expected)

        spec = "not match(ip_src=a.b.c.d); s14: .* s10 .* => (N-s10)* s11 (N-s10)* od NM:{s3}"
        expected = [('s7', 's2'), ('s14', 's7'), ('s11', 's19'), ('s2', 's11')]
        runSynthesis(FattreeTopo(), testFattree.config, spec, expected)

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

    def testDrop(self):
        config = NetworkConfig(paths=[('s4', 's1', ['s4', 's2', 's1'])],
                               egresses=['s1'])
        specstr = "not match(ip_src=a.b.c.d); s1: .* s2 .* => (N-s2) s3 (N-s2) od"
        expected = [('s1', 's3')]
        runSynthesis(DiamondTopo(), config, spec, expected)

class testSosr(unittest.TestCase):

    def testSosrFigure3(self):
        config = NetworkConfig(egresses=['Z'],
                               flowtable=[('A', '10.0.1.1', 'Z', 'F1'),
                                          ('B', '10.0.1.1', 'Z', 'F1'),
                                          ('C', '10.0.1.1', 'Z', 'F1'),
                                          ('F1', '10.0.1.1', 'Z', 'X'),
                                          ('X', '10.0.1.1', 'Z', 'Z'),
                                          ('F2', '10.0.1.1', 'Z', 'Y')])

        spec = "match(tcp_src_port=80); A,B,C: .* F1 .* => (N-F1)* F2 (N-F1)* od NM:{F1,F2}"
        expected = [('Y', 'Z'), ('B', 'F2'), ('C', 'F2'), ('A', 'F2')]
        runSynthesis(SosrTopo(), config, spec, expected)


class testThintree(unittest.TestCase):
    def testThinTree(self):
        config = NetworkConfig(egresses=['s10', 's11', 's1'],
                               paths=[('s1', 's10',
                                       ['s1', 's2', 's4', 's8', 's10'])])

        spec = "not match(ip_src=a.b.c.d); s1: .* s4 .* => (N-s4)(N-s4)* s5 (N-s4)(N-s4)*"
        expected = [('s2', 's5'), ('s5', 's8')]
        runSynthesis(ThintreeTopo(), config, spec, expected)

class testCluster(unittest.TestCase):

    def testCluster(self):
        config = NetworkConfig(egresses=['Dst'],
                               paths=[('Src', 'Dst',
                                       ['Src', 's14', 'Core', 's15', 'Dst'])])
        spec = "not match(ip_src=a.b.c.d); Src: .* Core .* => N* Fw1 N* od"
        expected = [('Fw1', 's18'), ('Core', 'Fw1'), ('s18', 's15')]
        runSynthesis(DiamondClusterTopo(), config, spec, expected)

if __name__ == "__main__":
    unittest.main()
