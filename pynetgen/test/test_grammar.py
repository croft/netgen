#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from grammar import SpecGrammar

class testGrammar(unittest.TestCase):

    def testDestination(self):
        spec = "match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s)* od NM:{s0}"
        parsed = SpecGrammar.parseString(spec)
        assert parsed is not None
        assert len(parsed[4]) > 0

        spec = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s)* NM:{s0}"
        parsed = SpecGrammar.parseString(spec)
        assert parsed is not None
        assert len(parsed[4]) == 0

    def testImmutable(self):
        spec = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s)*"
        parsed = SpecGrammar.parseString(spec)
        assert parsed is not None
        assert len(parsed[5]) == 0

        spec = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s)* NM:{s0}"
        parsed = SpecGrammar.parseString(spec)
        assert parsed is not None
        assert len(parsed[5]) == 1

        spec = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s)* NM:{s0, s1}"
        parsed = SpecGrammar.parseString(spec)
        assert parsed is not None
        assert len(parsed[5]) == 2

    def testPathCondition(self):
        spec = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s3 (N-s2)* NM:{s0, s1}"
        parsed = SpecGrammar.parseString(spec)
        assert " ".join(parsed[2]) == ".* s2 .*"
        assert " ".join(parsed[3]) == "(N-s2)* s3 (N-s2)*"
        assert len(parsed[2]) > 0
        assert len(parsed[3]) > 0

if __name__ == "__main__":
    unittest.main()
