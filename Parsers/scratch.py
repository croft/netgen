#!/usr/bin/env python

import FAdo.reex
from FAdo.reex import *

# create a parse class with a custom alphabet as the lexer id rule
def parser_factory(sigma):
    class ParseRegAlphabet(ParseReg1):
        def __init__(self, no_table=0, table='.tablereg'):
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
                        ("({0})".format("|".join(sigma)), lambda x: ("id", x)),
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

# =============================================================================
# working example with ascii alphabet
# =============================================================================
expr = "aa*|b"
re = str2regexp(expr)
dfa = re.toDFA()
dfa = dfa.completeMinimal()
print "REGEX:", expr
print "States:", dfa.States
print "Initial:", dfa.Initial
print "Final:", dfa.Final
print "Transitions:", dfa.succintTransitions()

print "\n---------------------------------------\n"

# =============================================================================
# working example with switch names
# =============================================================================
alphabet = ["s0", "s1"]
expr = "s0s0* s1 s0s0*"
re = str2regex_alpha(expr, alphabet)
dfa = re.toDFA()
#dfa = dfa.completeMinimal()
print "REGEX:", expr
print "States:", dfa.States
print "Initial:", dfa.Initial
print "Final:", dfa.Final
print "Transitions:", dfa.succintTransitions()

