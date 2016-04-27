#!/usr/bin/env python

import argparse
import os
import random
import re
import shutil
import string

import FAdo.reex
from FAdo.reex import *

# create a parse class with a custom alphabet as the lexer id rule
def parser_factory(sigma):
    class ParseRegAlphabet(ParseReg1):
        def __init__(self, no_table=0, table='.tablereg'):
            # sort by longest string length first:
            # yappy seems to stop on first matching id, so to prevent
            # matching a substring (which will raise an invalid regex error),
            # place substrings last
            siglist = sorted(list(sigma), key=len, reverse=True)
            grammar = [("r", ["r", "|", "c1"], self.OrSemRule),
                       ("r", ["c1"], self.DefaultSemRule),
                       ("c1", ["c1", Conj, "c2"], self.ConjSemRule),
                       ("c1", ["c2"], self.DefaultSemRule),
                       ("c2", ["c2", Shuffle, "c"], self.ShuffleSemRule),
                       ("c2", ["c"], self.DefaultSemRule),
                       ("c", ["c", "s"], self.ConcatSemRule),
                       ("c", ["s"], self.DefaultSemRule),
                       ("s", ["s", "*"], self.StarSemRule),
                       ("s", ["o"], self.DefaultSemRule),
                       ("o", ["o", Option], self.OptionSemRule),
                       ("o", ["f"], self.DefaultSemRule),
                       ("f", ["b"], self.DefaultSemRule),
                       ("f", ["(", "r", ")"], self.ParSemRule),
                       ("b", ["id"], self.BaseSemRule),
                       ("b", [EmptySet], self.BaseSemRule),
                       ("b", [Epsilon], self.BaseSemRule)]
            tokenize = [("\s+", ""),
                        (Epsilon, lambda x: (x, x)),
                        (EmptySet, lambda x: (x, x)),
                        (Shuffle, lambda x: (x, x)),
                        (Conj, lambda x: (x, x)),
                        (Option, lambda x: (x, x)),
                        # add custom alphabet
                        ("({0})".format("|".join(siglist)),
                         lambda x: ("id", x)),
                        # old id rule
                        #("[A-Za-z0-9]", lambda x: ("id", x)),
                        ("\|", lambda x: (x, x)),
                        ("\+", lambda x: ("|", x)),
                        ("\*", lambda x: (x, x)),
                        ("\(|\)", lambda x: (x, x))]
            Yappy.__init__(self, tokenize, grammar, table, no_table)

    return ParseRegAlphabet

# convert a string to regex using a custom alphabet
def str2regex_alpha(regex, alphabet):
    return str2regexp(regex,
                      parser=parser_factory(alphabet),
                      sigma=set(alphabet),
                      strict=True)

# convert set difference expression (eg, N-s0) into regex disjunction
def expand_regex(expr, topo):
    matches = re.finditer(r"(\w+)\s*-\s*(\w+)",
                          expr,
                          re.IGNORECASE|re.MULTILINE)
    for m in matches:
        if m.group(1).strip() != "N":
            print "Invalid syntax: {0} in {1}".format(m.group(1),
                                                      m.group(0))
            return None

        diff = topo.switch_diff(m.group(2))
        expr = expr.replace(m.group(0), "|".join(diff))

    return expr

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

    def match_classes(self, regex):
        matches = []
        for p, pc in self.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    matches.append(p)
                    break

        return sorted(matches, key=int)

class FSA(object):
    def __init__(self, regex, sigma):
        self.regex = regex
        if isinstance(sigma, list):
            self.sigma = set(sigma)
        else:
            self.sigma = sigma
        self.dfa = self._parse()
        self.states = FSA.state_names(self.dfa)
        self.symbols = FSA.symbol_names(self.dfa)
        self.final = FSA.pprint_state_name(self.dfa.Final)
        self.initial = FSA.pprint_state_name(self.dfa.Initial)
        self.transitions = FSA.transition_names(self.dfa)

    def _parse(self):
        expr = str2regex_alpha(self.regex, self.sigma)
        nfa = expr.toNFA()
        rnfa = nfa.reversal()
        dfa = rnfa.toDFA()
        dfa = dfa.completeMinimal()
        return dfa

    def __repr__(self):
        return str(self)

    def __str__(self):
        output = "[INFO] states: {0}\n".format(" ".join(self.states))
        output += "[INFO] start: {0}\n".format(" ".join(self.initial))
        output += "[INFO] symbols: {0}\n".format(" ".join(self.symbols))
        output += "[INFO] transitions:\n"
        output += "\n".join(["{0} {1} {2}".format(start, t, end)
                             for start, t, end in self.transitions])
        output += "\n"
        output += "[INFO] final: {0}".format(" ".join(self.final))
        return output

    @classmethod
    def pprint_state_name(cls, state):
        if isinstance(state, set):
            term = "/".join([str(s) for s in state])
            return term

        return str(state)

    @classmethod
    def state_names(cls, dfa):
        states = []
        for subset in dfa.States:
            term = FSA.pprint_state_name(subset)
            if term not in states:
                states.append(term)

        return states

    @classmethod
    def symbol_names(cls, dfa):
        symbols = []
        for t in dfa.succintTransitions():
            start, symbol, end = t
            tokens = symbol.split(",")
            for token in tokens:
                token = token.strip()
                if token not in symbols:
                    symbols.append(token)

        return sorted(symbols)

    @classmethod
    def transition_names(cls, dfa):
        lines = []
        state_names = {}
        for s in dfa.States:
            state_names[str(s)] = FSA.pprint_state_name(s)

        for t in dfa.succintTransitions():
            start, symbol, end = t
            tokens = symbol.split(",")
            for token in tokens:
                token = token.strip()
                lines.append((state_names[start],
                              token,
                              state_names[end]))

        return lines

class Specification(object):
    def __init__(self, spec):
        self.spec = spec.strip()
        tokens = self.spec.split("=>")
        if len(tokens) > 2 or len(tokens) < 1:
            raise Exception("Invalid specification {0}".format(self.spec))

        self.lhs = tokens[0].strip()
        self.rhs = None
        if len(tokens) > 1:
            self.rhs = tokens[1].strip()

    def parse(self, network, destination):
        self._parse_lhs(network, destination)
        self._parse_rhs(network, destination)

    def _parse_lhs(self, network, destination):
        # clean select dir
        select_dir = os.path.join(destination, "selected")
        if os.path.exists(select_dir):
            shutil.rmtree(select_dir)

        os.makedirs(select_dir)

        regex = expand_regex(self.lhs, network.topo)
        matches = network.match_classes(regex)
        for m in matches:
            shutil.copy2(network.class_files[m], select_dir)

    def _parse_rhs(self, network, destination):
        destination = os.path.join(destination, "automata.txt")
        regex = expand_regex(self.rhs, network.topo)
        fsa = FSA(regex, network.topo.switches)
        with open(destination, 'w') as f:
            f.write(str(fsa))

def main():
    default_dest = "./output"
    default_spec = "./spec.txt"
    default_class = "./VeriFlow-v0.2/VeriFlow/class"
    parser = argparse.ArgumentParser(description="NetGen specification parser")
    parser.add_argument("--destination", "-d", dest="dest",
                        default=default_dest,
                        help="output file destination (default: %s)" % default_dest)
    parser.add_argument("--spec", "-s", dest="spec",
                        default="spec.txt",
                        help="specification file (default: %s)" % default_spec)
    parser.add_argument("--classes", "-c", dest="class_dir",
                        default=default_class,
                        help="packet class directory (default: %s)" % default_class)

    args = parser.parse_args()

    if not os.path.isfile(args.spec):
        print "Specification file {0} does not exist!".format(args.spec)
        return

    if not os.path.isdir(args.class_dir):
        print "Packet class directory {0} does not exist!".format(
            args.class_dir)
        return

    if not os.path.isdir(args.dest):
        os.makedirs(args.dest)

    network = Network(args.class_dir)
    print "Loaded network with {0} packet classes".format(
        len(network.classes.keys()))

    spec = Specification(open(args.spec).read())
    spec.parse(network, args.dest)

if __name__ == "__main__":
    main()
