#!/usr/bin/env python

# GRAMMAR
# (Note: traffic and path specs now separated by semicolon)
# ----------------------------------------------------------
# spec ::= traffic; S: path => path[od] [NM:R]
#
# traffic ts ::= true |
#                match(header=val) |
#                match(header,prefix) |
#                (ts & ts) |
#                (not ts)
#
# path p ::= n | . | p + p | p p | p*
#
# n ::= alpha
# ----------------------------------------------------------

import abc
from pyparsing import Word, alphas, Literal, Group, alphanums

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

ARROW = Literal("=>")
EQUAL = Literal("=")
LPAREN = Literal("(")
RPAREN = Literal(")")
COMMA = Literal(",")
COLON = Literal(";")
MATCH = Literal("match")

HEADER_WORDS = Word(alphanums+"_.")

EXACT_MATCH = Group(MATCH.suppress() +
                    LPAREN.suppress() +
                    HEADER_WORDS +
                    Literal("=") +
                    HEADER_WORDS +
                    RPAREN.suppress()
                )

PREFIX_MATCH = Group(MATCH.suppress() +
                     LPAREN.suppress() +
                     HEADER_WORDS +
                     Literal(",") +
                     HEADER_WORDS +
                     RPAREN.suppress()
                 )

TRAFFIC_CORE = (Literal("true") |
                EXACT_MATCH |
                PREFIX_MATCH)

# TODO: encode conjunction as (ts&ts) or ts&ts?
TRAFFIC = Group(TRAFFIC_CORE + Literal("&") + TRAFFIC_CORE |
           Literal("not") + TRAFFIC_CORE |
           TRAFFIC_CORE)

PATH = Group(Word(alphanums+"()_.*- "))

grammar = (TRAFFIC +
           COLON.suppress() +
           PATH +
           ARROW.suppress() +
           PATH)

test = "not match(ip_src=a.b.c.d); .* s2 .* => (N-s2)* s2 (N-s2)*"
parsed = grammar.parseString(test)
t = TrafficSpec(parsed[0])
print "Traffic:", t
print "Path lhs:", parsed[1]
print "Path rhs:", parsed[2]
