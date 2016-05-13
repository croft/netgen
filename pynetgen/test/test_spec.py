#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from spec import Specification, expand_regex
from topos import DiamondTopo

class testSpecification(unittest.TestCase):

    def testSpec(self):
        specstr = "match(ip_src=a.b.c.d); s1: .* s2 .* => (N-s2)* s3 (N-s2)* od NM:{s4}"
        spec = Specification.parseString(DiamondTopo(), specstr)
        assert spec.od == True
        assert len(spec.sources) == 1 and spec.sources[0] == 's1'
        assert len(spec.immutables) == 1 and spec.immutables[0] == 's4'

    def testSpecNoOdNm(self):
        specstr = "match(ip_src=a.b.c.d); s1: .* s2 .* => (N-s2)* s3 (N-s2)*"
        spec = Specification.parseString(DiamondTopo(), specstr)
        assert spec.od == False
        assert len(spec.immutables) == 0

    def testSpecInvalidNodes(self):
        specstr = "match(ip_src=a.b.c.d); s5: .* s2 .* => (N-s2)* s3 (N-s2)*"
        with self.assertRaises(Exception):
            spec = Specification.parseString(DiamondTopo(), specstr)

    def testRegexExpansion(self):
        topo = DiamondTopo()
        aliases = { "N" : topo.switches.keys(),
                    "FW" : ['s1', 's2']
                }

        expanded = expand_regex("N-s1", topo, aliases)
        assert expanded == "s2|s3|s4"

        expanded = expand_regex("FW-s1", topo, aliases)
        assert expanded == "s2"

        with self.assertRaises(Exception):
            expanded = expand_regex("FW2-s1", topo, aliases)

    def testRegexExpansionIpNaming(self):
        class FakeTopo(object):
            def __init__(self, sw):
                self.switches = dict((k, None) for k in sw)

        aliases = { 'N' : ['10.0.0.1', '10.0.0.150']}
        topo = FakeTopo(aliases['N'])
        expanded = expand_regex("(N-10.0.0.150)*", topo, aliases)
        assert expanded == "(10.0.0.1)*"

if __name__ == "__main__":
    unittest.main()
