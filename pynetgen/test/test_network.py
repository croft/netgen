#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from network import PacketClass
from trie import Rule, ForwardingGraph, ForwardingLink

class testPacketClass(unittest.TestCase):

    def testAllPossiblePathsConstruction(self):
        r1 = Rule()
        r1.location = "s1"
        r1.nextHop = "s2"

        r2 = Rule()
        r2.location = "s1"
        r2.nextHop = "s3"

        r3 = Rule()
        r3.location = "s2"
        r3.nextHop = "s4"

        fg = ForwardingGraph()
        fg.addLink(ForwardingLink(r1))
        fg.addLink(ForwardingLink(r2))
        fg.addLink(ForwardingLink(r3))

        p = PacketClass(fg, None, 1)

        paths = p.construct_strings()
        print paths
        expected = ['s2 s4', 's1 s2 s4', 's1 s3']

        assert len(paths) == len(expected)
        for e in expected:
            assert e in paths

if __name__ == "__main__":
    unittest.main()
