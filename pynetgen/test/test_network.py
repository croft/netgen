#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from network import PacketClass

class testPacketClass(unittest.TestCase):

    def testAllPossiblePathsConstruction(self):
        p = PacketClass(1)
        p.edges["s1"] = ["s2", "s3"]
        p.edges["s2"] = ["s4"]

        paths = p.construct_strings()
        expected = ['s2 s4', 's1 s2 s4', 's1 s3']

        assert len(paths) == len(expected)
        for e in expected:
            assert e in paths
