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

from pyparsing import Word, alphas, Literal, Group, alphanums, ZeroOrMore

ARROW = Literal("=>")
EQUAL = Literal("=")
LPAREN = Literal("(")
RPAREN = Literal(")")
COMMA = Literal(",")
SEMICOLON = Literal(";")
COLON = Literal(":")
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

SOURCES = Group(Word(alphanums+"_.") + ZeroOrMore(COMMA.suppress() + Word(alphanums+"_.")))

SpecGrammar = (TRAFFIC +
               SEMICOLON.suppress() +
               SOURCES +
               COLON.suppress() +
               PATH +
               ARROW.suppress() +
               PATH)

# test = "not match(ip_src=a.b.c.d); h1: .* s2 .* => (N-s2)* s2 (N-s2)*"
# parsed = grammar.parseString(test)
# t = TrafficSpec(parsed[0])
# print "Traffic:", t
# print "Sources:", parsed[1]
# print "Path lhs:", parsed[2]
# print "Path rhs:", parsed[3]
