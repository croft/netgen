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

from pyparsing import *

ARROW = Literal("=>")
EQUAL = Literal("=")
LPAREN = Literal("(")
RPAREN = Literal(")")
LBRACKET = Literal("{")
RBRACKET = Literal("}")
COMMA = Literal(",")
SEMICOLON = Literal(";")
COLON = Literal(":")
MATCH = Keyword("match")
OD = Keyword("od")
DROP = Keyword("drop")
NM = Keyword("NM")

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

LHS_PATH = Group(OneOrMore(Word(alphanums+"()_.*-")))

RHS_PATH = Group(ZeroOrMore(~OD + ~DROP + ~NM + Word(alphanums+"()_.*-")) + \
                 Optional(FollowedBy(OD)) | Optional(FollowedBy(DROP)) |
                 Optional(FollowedBy(NM)))

SOURCES = Group(Word(alphanums+"_.") + ZeroOrMore(COMMA.suppress() + Word(alphanums+"_.")))

ORIG_DEST = Group(Optional(OD))

DROP_GROUP = Group(Optional(DROP))

IMMUTABLE_CORE = NM.suppress() + COLON.suppress() + LBRACKET.suppress() + \
                 Word(alphanums+"_.") + \
                 ZeroOrMore(COMMA.suppress() + Word(alphanums+"_.")) + \
                 RBRACKET.suppress()

IMMUTABLES = Group(Optional(IMMUTABLE_CORE))

SpecGrammar = (TRAFFIC +
               SEMICOLON.suppress() +
               SOURCES +
               COLON.suppress() +
               LHS_PATH +
               ARROW.suppress() +
               RHS_PATH +
               ORIG_DEST +
               DROP_GROUP +
               IMMUTABLES)
