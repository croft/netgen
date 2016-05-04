#!/usr/bin/env python

from grammar import SpecGrammar
from spec import TrafficSpec

def test_grammar():
    test = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s2 (N-s2)* od NM:{s0,s1}"
    parsed = SpecGrammar.parseString(test)
    t = TrafficSpec(parsed[0])
    print "Traffic:", t
    print "Sources:", parsed[1]
    print "Path lhs:", parsed[2]
    print "Path rhs:", parsed[3]
    print "od:", len(parsed[4]) > 0
    print "NM:", parsed[5]

if __name__ == "__main__":
    test_grammar()
