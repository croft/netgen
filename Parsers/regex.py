#!/usr/bin/env python

import os
import re

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
            raise Exception("Missing {0} file".format(os.path.join(class_dir, "topo.txt")))
        
        self.topo = Topology(os.path.join(class_dir, "topo.txt"))
        
        for f in files:
            fname = os.path.splitext(os.path.basename(f))[0]
            self.classes[fname] = PacketClass(f)
            self.class_files[fname] = f

class Regex(object):
    def __init__(self, spec):
        self.spec = spec

    @classmethod
    def expand(cls, regex, topo):
        matches = re.finditer(r"(\w+)\s*-\s*(\w+)", regex, re.IGNORECASE|re.MULTILINE)
        for m in matches:
            if m.group(1).strip() != "N":
                print "Invalid syntax: {0} in {1}".format(m.group(1), m.group(0))
                return None

            diff = topo.switch_diff(m.group(2))
            regex = regex.replace(m.group(0), "|".join(diff))

        return regex

    def match(self, network):
        regex = Regex.expand(self.spec, network.topo)
        matches = []
        for p, pc in network.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    matches.append(p)
                    break

        return sorted(matches, key=int)
        
path="VeriFlow-v0.2/VeriFlow/class"
n = Network(path)
r = Regex(r"(N - s12)* s12 (N - s12)*")
m = r.match(n)
print n.class_files[m[0]]
