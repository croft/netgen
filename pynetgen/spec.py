#!/usr/bin/env python

import abc
import argparse
import os
import re
import shutil
import ConfigParser

from FAdo.reex import *

from grammar import SpecGrammar

# create a parse class with a custom alphabet as the lexer id rule
def parser_factory(sigma):
    class ParseRegAlphabet(ParseReg1):
        def __init__(self, no_table=0, table='.tablereg'):
            # sort by longest string first:
            # matching on a substring will raise an invalid regex error,
            # and since yappy seems to stop on first matching id,
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
def expand_regex(expr, topo, aliases):
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

    for alias, values in aliases.iteritems():
        expr = expr.replace(alias, "({0})".format("|".join(values)))

    return expr

class FSA(object):
    def __init__(self, regex, sigma):
        self.regex = regex
        if isinstance(sigma, list):
            self.sigma = set(sigma)
        else:
            self.sigma = sigma

        self.renameCount = 0
        self.dfa = self._parse()
        self.states = FSA.state_names(self.dfa)
        self.symbols = FSA.symbol_names(self.dfa)
        self.transitions = FSA.transition_names(self.dfa)
        self.final = [self.pprint_state_name(self.dfa.States[x])
                      for x in self.dfa.Final]
        self.initial = self.dfa.States[self.dfa.Initial]
        self.symbolAliases = {}

        symcount = 0
        for s in sorted(self.symbols):
            self.symbolAliases[s] = symcount
            symcount += 1

    def _parse(self):
        expr = str2regex_alpha(self.regex, self.sigma)
        nfa = expr.nfaFollow()
        rnfa = nfa.reversal()
        dfa = rnfa.toDFA()
        dfa = dfa.minimal(complete=True)
        self.renameCount = len(dfa.States)

        for i in range(len(dfa.States)):
            state = dfa.States[i]
            if state == 'dead':
                dfa.renameState(i, 0)
            else:
                #if isinstance(state, set):
                self.renameCount += 1
                dfa.renameState(i, self.renameCount)

        # add transitions: (dead, any, dead)
        for i in range(len(dfa.States)):
            dfa.addTransition(i, 0, dfa.stateIndex(0))

        # add transitions: (final, any, dead)
        for f in dfa.Final:
            for s in FSA.symbol_names(dfa):
                if dfa.Delta(f, s) is not None:
                    dfa.delTransition(f, s, dfa.Delta(f,s))
                dfa.addTransition(f, s, dfa.stateIndex(0))

        print dfa.succintTransitions()
        print dfa.States[dfa.Initial]
        print map(lambda x:dfa.States[x], dfa.Final)
        return dfa

    def __repr__(self):
        return str(self)

    def __str__(self):
        output = "[INFO] states: {0}\n".format(" ".join(self.states))
        output += "[INFO] start: {0}\n".format(self.initial)
        output += "[INFO] symbols: {0}\n".format(" ".join(self.symbols))
        output += "[INFO] transitions:\n"
        output += "\n".join(["{0} {1} {2}".format(start, t, end)
                             for start, t, end in self.transitions])
        output += "\n"
        output += "[INFO] final: {0}\n".format(" ".join(self.final))
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

class HeaderMatch(object):
    __metaclass__ = abc.ABCMeta

    NW_SRC = "IP_SRC"
    NW_DST = "IP_DST"
    DL_SRC = "MAC_SRC"
    DL_DST = "MAC_DST"
    TP_SRC = "TCP_SRC_PORT"
    TP_DST = "TCP_DST_PORT"
    Fields = [NW_SRC, NW_DST, DL_SRC, DL_DST, TP_SRC, TP_DST]

    def __init__(self, name, value):
        if name.upper() not in HeaderMatch.Fields:
            raise Exception("Invalid header field {0}".format(name))

        self.name = name
        self.value = value

    @abc.abstractmethod
    def evaluate(self, rule):
        return False

    def field_value(self, field):
        # TODO: depends on packet class
        pass

    def __repr__(self):
        return str(self)

class ExactMatch(HeaderMatch):
    def __init__(self, name, value):
        super(ExactMatch, self).__init__(name, value)

    def evaluate(self, rule):
        # TODO
        pass

    def __str__(self):
        return "{0}={1}".format(self.name,
                                self.value)

class PrefixMatch(object):
    def __init__(self, name, value):
        super(PrefixMatch, self).__init__(name, value)

    def evaluate(self, rule):
        # TODO
        pass

    def __str__(self):
        return "{0},{1}".format(self.name,
                                self.value)

class TrafficSpec(object):
    NOT = "not"
    AND = "&"

    def __init__(self, parsed_strings):
        self.terms = [TrafficSpec.traffic_factory(ts)
                      for ts in parsed_strings]

    def match(self, rules):
        # TODO
        pass

    @classmethod
    def traffic_factory(cls, ts):
        if isinstance(ts, str) and ts in [TrafficSpec.NOT,
                                          TrafficSpec.AND]:
            return ts
        elif ts[1] == "=":
            return ExactMatch(ts[0], ts[2])
        elif ts[1] == ",":
            return PrefixMatch(ts[0], ts[2])
        else:
            raise Exception("Invalid traffic spec {0}".format(ts))

    def __repr__(self):
        return str(self)

    def __str__(self):
        return " ".join(str(term) for term in self.terms)

class Specification(object):
    def __init__(self, spec_file):
        self.spec_file = spec_file
        self.spec_str = None
        self.ts = None
        self.sources = None
        self.lhs = None
        self.rhs = None
        self.aliases = {}
        self.matched_classes = []
        self.fsa = None
        print "Found aliases:", self.aliases.keys()

    def parse(self, network, destination):
        cfg = ConfigParser.ConfigParser()
        cfg.read(self.spec_file)

        for name, value in cfg.items("aliases"):
            if name not in self.aliases:
                self.aliases[name] = []
            self.aliases[name].extend([v.strip() for v in value.split(",")])

        if len(cfg.items("change")) == 0:
            raise Exception("Missing required section [change]")

        change_re = re.search(r"\[change\]([\s\S]+)(\[\w+]|$)",
                              open(self.spec_file, 'r').read(),
                              re.MULTILINE)
        if change_re:
            self.spec_str = change_re.group(1).replace("\n", "").strip()
        else:
            raise Exception("Unable to parse [change] section")

        parsed = SpecGrammar.parseString(self.spec_str)
        # TODO: process traffic spec, sources

        self.sources = parsed[1]

        if len(parsed[2]) > 1:
            raise Exception("lhs error")
        if len(parsed[3]) > 1:
            raise Exception("rhs error")

        self.lhs = parsed[2][0].strip()
        self.rhs = parsed[3][0].strip()

        self._parse_lhs(network, destination)
        self._parse_rhs(network, destination)

        # TODO: better place for this
        network.topo.make_topofile(destination, topofile="Topology.txt")
        network.topo.make_configmap(destination)

    def _parse_lhs(self, network, destination):
        # clean select dir
        select_dir = os.path.join(destination, "selected")
        if os.path.exists(select_dir):
            shutil.rmtree(select_dir)
        os.makedirs(select_dir)

        regex = expand_regex(self.lhs, network.topo, self.aliases)
        print "Lhs expanded:", regex

        self.matched_classes = network.match_classes(regex)
        for c in self.matched_classes:
            print "Matched packet class:", c
            with open(os.path.join(select_dir, "{0}.txt".format(c)), 'w') as f:
                f.write(str(network.classes[c]))

    def _parse_rhs(self, network, destination):
        destination = os.path.join(destination, "automata.txt")
        regex = expand_regex(self.rhs, network.topo, self.aliases)
        print "Rhs expanded:", regex
        self.fsa = FSA(regex, network.topo.switches)
        print str(self.fsa)
        with open(destination, 'w') as f:
            f.write(str(self.fsa))

    def __repr__(self):
        return str(self)

    def __str__(self):
        return self.spec_str

if __name__ == "__main__":
    parsed = SpecGrammar.parseString("not match(ip_src=a.b.c.d); h1, h2: .* s1 .* => (N-s1) s2 (N-s1)")
    for i, p in enumerate(parsed):
        print i, p