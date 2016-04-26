#!/usr/bin/env python

import os
import random
import re
import shutil
import string

import pyfsa.FSA as FSA

class Topology(object):
    def __init__(self, fname):
        self.edges = Topology.get_edges(fname)

        # TODO: better way to filter hosts
        self.switches = [s for s in self.edges.keys() if s[0] != 'h']

    @classmethod
    def get_edges(cls, fname, offset=0):
        edges = {}
        with open(fname) as f:
            for line in f.readlines():
                tokens = line.strip().split()
                edges[tokens[offset]] = tokens[offset+1]

        return edges

    def switch_diff(self, diff):
        if not isinstance(diff, list):
            diff = [diff]

        return [s for s in self.switches if s not in diff]

class PacketClass(object):
    def __init__(self, fname):
        self.edges = Topology.get_edges(fname, 1)

    def construct_strings(self):
        strings = []
        for key in self.edges.keys():
            s = []
            term = key
            while term in self.edges.keys():
                s.append(term)
                term = self.edges[term]

            s.append(term)
            strings.append(" ".join(s))

        return strings

class Network(object):
    def __init__(self, class_dir):
        self.classes = {}
        self.class_files = {}
        self.topo = None

        files = [os.path.join(class_dir, f) for f in os.listdir(class_dir)
                 if os.path.isfile(os.path.join(class_dir, f))
                 and os.path.splitext(f)[1] == '.txt'
                 and f != "topo.txt"]

        if not os.path.isfile(os.path.join(class_dir, "topo.txt")):
            raise Exception("Missing {0} file"
                            .format(os.path.join(class_dir, "topo.txt")))

        self.topo = Topology(os.path.join(class_dir, "topo.txt"))

        for f in files:
            fname = os.path.splitext(os.path.basename(f))[0]
            self.classes[fname] = PacketClass(f)
            self.class_files[fname] = f

class PacketSpecification(object):
    def __init__(self, regex):
        self.regex = regex

    @classmethod
    def expand(cls, regex, topo):
        matches = re.finditer(r"(\w+)\s*-\s*(\w+)",
                              regex,
                              re.IGNORECASE|re.MULTILINE)
        for m in matches:
            if m.group(1).strip() != "N":
                print "Invalid syntax: {0} in {1}".format(m.group(1),
                                                          m.group(0))
                return None

            diff = topo.switch_diff(m.group(2))
            regex = regex.replace(m.group(0), "|".join(diff))

        return regex

    def match(self, network):
        regex = PacketSpecification.expand(self.regex, network.topo)
        matches = []
        for p, pc in network.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    matches.append(p)
                    break

        return sorted(matches, key=int)

class ChangeSpecification(object):
    def __init__(self, regex):
        self.regex = regex
        self.terms = {}

    @classmethod
    def generate_term(cls, alpha=None, length=2):
        if alpha is None:
            alpha = string.ascii_lowercase + string.ascii_uppercase

        return ''.join(random.choice(alpha) for _ in range(length))

    @classmethod
    def rewrite(cls, regex, topo):
        terms = {}
        matched = []
        matches = re.finditer(r"(\w+)\s*-\s*(\w+)",
                              regex,
                              re.IGNORECASE|re.MULTILINE)
        for m in matches:
            if m.group(1).strip() != "N":
                print "Invalid syntax: {0} in {1}".format(m.group(1),
                                                          m.group(0))
                return (None, None)

            # skip duplicates
            if m.group(0) in matched:
                continue

            # in case we randomly generate an existing node's name
            replacement = ChangeSpecification.generate_term()
            while replacement in topo.switches + ['OD', 'od']:
                replacement = ChangeSpecification.generate_term()

            terms[replacement] = (m.group(0), m.group(1), m.group(2))
            regex = regex.replace(m.group(0), replacement)
            matched.append(m.group(0))

        return (regex, terms)

    def to_fsa(self, network):
        # regex, terms = ChangeSpecification.rewrite(self.regex, network.topo)
        # fsa = FSA.compileRE(regex, terms.keys() + network.topo.switches)
        # fsa = FSA.reverse(fsa)
        # print fsa

        regex = PacketSpecification.expand(self.regex, network.topo)
        print regex
        fsa = FSA.compileRE(regex, network.topo.switches)
        print fsa
        fsa = FSA.reverse(fsa)
        print fsa

class Specification(object):
    def __init__(self, spec):
        self.spec = spec.strip()
        tokens = self.spec.split("=>")
        if len(tokens) > 2:
            raise Exception("Invalid specification {0}".format(self.spec))

        self.lhs = PacketSpecification(tokens[0].strip())
        self.rhs = None
        if len(tokens) > 1:
            self.rhs = ChangeSpecification(tokens[1].strip())

    def parse(self, network):
        self._parse_lhs(network)
        self._parse_rhs(network)

    def _parse_lhs(self, network):
        # clean select dir
        select_dir = "selected"
        if os.path.exists(select_dir):
            shutil.rmtree(select_dir)

        os.makedirs(select_dir)

        matches = self.lhs.match(network)
        for m in matches:
            shutil.copy2(network.class_files[m], "selected")

    def _parse_rhs(self, network):
        transitions = self.rhs.to_fsa(network)

def print_fsa(fsa):
    fsa = fsa.determinized()
    fsa = fsa.minimized()
    print "[INFO] states:", " ".join([str(s) for s in fsa.states])
    print "[INFO] start:", fsa.initialState
    print "[INFO] symbols:",  " ".join(set([str(s[2]) for s in fsa.transitions if s[2][0] != '~']))
    for t in fsa.transitions:
        # ignore 'not' lables
        if t[2][0] != '~':
            print t[0], t[1], t[2]
    print "[INFO] final:", " ".join([str(s) for s in fsa.finalStates])
    print "-------------------------"
    print fsa

def test():
    path="VeriFlow-v0.2/VeriFlow/class"
    network = Network(path)
    spec = Specification(r".* s0 .* => (N - s0)+ s2 (N - s0)+")
    spec.parse(network)

def test_fsa():
    fsa = FSA.compileRE(".*A.*B C.*")
    # print_fsa(FSA.reverse(fsa))
    print_fsa(fsa)

    fsa = FSA.compileRE("(a|b|c|d)+ e (a|b|c|d)+")
    print fsa

    # dfa = fsa.determinized()
    # rev = FSA.reverse(dfa)
    # f = FSA.reverse(f)
    # print f
    # print f.states
    # print f.finalStates
    # print f.labels()
    # print dir(f)

if __name__ == "__main__":
    test()
#    test_fsa()
