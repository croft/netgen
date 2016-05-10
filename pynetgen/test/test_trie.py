#!/usr/bin/env python

import unittest

from runner import addPath
addPath()

from fields import HeaderField, ip2int, wc2ip
from trie import MultilevelTrie, Rule

def parse_switch_file(fname):
    rules = []
    with open(fname) as f:
        for line in f.readlines():
            tokens = line.split()
            dst = tokens[2]
            wc = tokens[3]
            nexthop = tokens[5]
            priority = int(tokens[7])
            if '/' in dst:
                dst_tokens = dst.split('/')
                block = int(dst_tokens[1])
                dst = dst_tokens[0]
                if wc2ip(32-block) != wc:
                    raise Exception("Error: inconsistency in wildcard")
            r = Rule()
            r.ruleType = Rule.FORWARDING
            r.fieldValue[HeaderField.Index["NW_DST"]] = ip2int(dst)
            r.fieldMask[HeaderField.Index["NW_DST"]] = ip2int(wc)
            r.priority = priority
            r.nextHop = nexthop
            r.location = tokens[4]
            rules.append(r)
    return rules

class testTrie(unittest.TestCase):

    def testEquivalenceClasses(self):
        cases = [("../data_set/RocketFuel/AS-1755/R10.0.5.114", 2728),
                 ("../data_set/RocketFuel/AS-1755/R10.0.5.162", 55828),
                 ("../data_set/RocketFuel/AS-1755/R10.0.4.26", 175443)]

        for fname, numclasses in cases:
            tr = MultilevelTrie()
            rules = parse_switch_file(fname)
            for rule in rules:
                tr.addRule(rule)

            eqclasses = tr.getAllEquivalenceClasses()
            assert len(eqclasses) == numclasses
