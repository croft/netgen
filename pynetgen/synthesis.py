#!/usr/bin/env python

import abc
from z3 import *

class AbstractNetwork(object):
    def __init__(self, concrete_network, spec):
        self.concrete_network = concrete_network
        topo = concrete_network.topo
        classes = concrete_network.classes.values()

        self.edges = []
        self.rules = {}

        self.node_strrep = {}
        self.node_intrep = {}
        self.class_pcrep = {}

        # switch renaming
        for switch in topo.switches.keys():
            # TODO: clean this up
            alias = spec.fsa.symbolAliases[switch]
            self.node_strrep[alias] = switch
            self.node_intrep[switch] = alias

        # packet class renaming
        idx = 1
        for pc in classes:
            self.class_pcrep[idx] = pc
            idx += 1

        for src, dst in topo.iteredges():
            # end host or external node
            if src not in self.node_intrep.keys() or \
               dst not in self.node_intrep.keys():
                continue

            self.edges.append((self.node_intrep[src],
                               self.node_intrep[dst]))

        # add drop node
        for switch in self.node_strrep.keys():
            self.edges.append((switch, 0))
            # self.edges.append((0, switch))

        # set default value 0
        for switch in self.node_strrep.keys():
            self.rules[switch] = {}
            for pcid in self.class_pcrep.keys():
                self.rules[switch][pcid] = 0

        for pcid, pc in self.class_pcrep.iteritems():
            for src, dst in pc.iteredges():
                src_int = self.node_intrep[src]
                dst_int = self.node_intrep[dst]
                self.rules[src_int][pcid] = dst_int

        self.sources = [self.node_intrep[s] for s in spec.sources]
        self.immutable = [self.node_intrep[s] for s in spec.immutables]
        self.sinks = [self.node_intrep[s] for s in topo.egresses()]

    @property
    def nodes(self):
        return self.node_strrep.keys()

    @property
    def classes(self):
        return self.class_pcrep.keys()

class Synthesizer(object):
    def __init__(self, network, spec):
        self.network = AbstractNetwork(network, spec)
        self.spec = spec
        self.fsa = spec.fsa
        # print "Nodes: ", self.network.node_strrep.keys()
        # print "Rules: ", self.network.rules
        # print "Classes: ", self.network.classes
        # print "Sources: ", self.nework.sources
        # raise Exception("blah")

    def path_solution(self, model):
        varnames = {}
        for g in model:
            if str(g)[0] == 'n':
                varnames[str(g)] = model[g]

        links = []
        for i in range(len(varnames.keys())/2):
            from_name = "n_{0}".format(i)
            to_name = "n1_{0}".format(i)
            links.append((varnames[from_name], varnames[to_name]))

        # convert int representation to string
        # TODO: better way to convert to int?
        return [(self.network.node_strrep[int(str(f))],
                 self.network.node_strrep[int(str(t))])
                for (f, t) in links]

    def solve(self):
        for i in range(len(self.network.nodes)):
        # for i in range(2,3):
            print "-------------------------------------------"
            print "        Phase:", i+1
            print "-------------------------------------------"
            query = SmtQuery(self.fsa, self.network, i+1, self.spec)
            query.define_k_rules()
            query.delta_sat_topo()

            cycle = Function("cycle", IntSort(), IntSort(), IntSort())
            query.exec_recursion(Cyclicity(cycle))

            dest = Function("dest", IntSort(), IntSort(), IntSort())
            query.exec_recursion(ComputeDestination(dest, self.network, self.spec))

            rho = Function("rho", IntSort(), IntSort(), IntSort())
            delta = Function("delta", IntSort(), IntSort(), IntSort())
            query.exec_recursion(ModifiedFunctionality(rho,
                                                       delta,
                                                       self.fsa,
                                                       self.network.nodes))

            query.accept_automata(rho)
            model = query.solve()
            if model is not None:
                print "\n**********************************"
                print "*  MODEL FOUND"
                print "**********************************"
                path = self.path_solution(model)
                print path
                # print model
                # print model[dest]
                # print model[rho]
                # print model[cycle]
                # print model[delta]
                break


class SmtQuery(object):
    def __init__(self, fsa, network, k, spec):
        self.fsa = fsa
        self.network = network
        self.k = k
        self.spec = spec

        self.p = []
        self.n = []
        self.n1 = []

        self.solver = Solver()
        self.solver.reset()
        self.query = BoolVal(True)

    def solve(self):
        self.solver.add(self.query)
        print self.solver.sexpr()
        if self.solver.check() == sat:
            return self.solver.model()
        else:
            return None

    def enforce_immutability(self):
        # TODO: rules for immutable nodes and classes not in specpc
        pass

    def delta_sat_topo(self):
        topostr = "(define-fun topology ((node_from Int) (node_to Int)) Bool \n"
        lparens = 0

        for from_node, to_node in self.network.edges:
            topostr += " ( ite ( and ( = node_from {0} ) ( = node_to {1} )) true \n".format(from_node, to_node)
            lparens += 1

        topostr += " false"
        topostr += ")" * (lparens+1)
        topostr += "\n"

        for i in range(self.k):
            topostr += "\n (declare-const {0} Int)".format(self.n[i])
            topostr += "\n (declare-const {0} Int)".format(self.n1[i])
            topostr += "\n (assert (topology {0} {1}))".format(self.n[i], self.n1[i])

        print topostr
        self.query = And(self.query, parse_smt2_string(topostr, ctx=main_ctx()))

    def define_k_rules(self):
        for i in range(self.k):
            n_str = "n_{0}".format(i)
            p_str = "p_{0}".format(i)
            n1_str = "n1_{0}".format(i)

            n_const = Const(n_str, IntSort())
            self.n.append(n_const)
            self.query = And(self.query, 0 < n_const)
            self.query = And(self.query, n_const <= len(self.network.nodes))

            p_const = Const(p_str, IntSort())
            self.p.append(p_const)
            self.query = And(self.query, 0 < p_const)
            self.query = And(self.query, p_const <= len(self.network.classes))

            n1_const = Const(n1_str, IntSort())
            self.n1.append(n1_const)
            self.query = And(self.query, 0 < n1_const)
            self.query = And(self.query, n1_const <= len(self.network.nodes))

    def exec_recursion(self, func):
        for pc in self.network.classes:
            self.query = And(self.query, func.auxiliary_def())
            self.query = And(self.query, func.encode_null(pc))

            for node in self.network.nodes:
                if node in self.network.sinks:
                    self.query = And(self.query, func.base(node, pc))
                else:
                    notnew = BoolVal(True)
                    for i in range(self.k):
                        self.query = And(self.query,
                                         Implies(And(node == self.n[i],pc == self.p[i]),
                                                 func.recurse(node, pc, self.n1[i])))
                        notnew = And(notnew,
                                     Or(node != self.n[i], pc != self.p[i]))

                    # TODO: reversing rules isn't needed? rev_rules
                    nexthop = self.network.rules[node][pc]
                    self.query = And(self.query,
                                     Implies(notnew, func.recurse(node,
                                                                  pc,
                                                                  nexthop)))

    def accept_automata(self, rho):
        for pc in self.network.classes:
            for src in self.network.sources:
                eachsrc = BoolVal(False)
                for final in self.fsa.final:
                    eachsrc = Or(eachsrc, rho(src, pc) == final)

                self.query = And(self.query, eachsrc)

class RecursiveDefinition(object):
    __metaclass__ = abc.ABCMeta

    @abc.abstractmethod
    def base(self, i, j):
        return

    @abc.abstractmethod
    def recurse(self, i, j, expr):
        return

    @abc.abstractmethod
    def auxiliary_def(self):
        return

    @abc.abstractmethod
    def encode_null(self, i):
        return

class Cyclicity(RecursiveDefinition):
    def __init__(self, cycle):
        self.cycle = cycle

    def base(self, node, pc):
        return self.cycle(node, pc) == 0

    def recurse(self, node, pc, n_to):
        return self.cycle(node, pc) > self.cycle(n_to, pc)

    def auxiliary_def(self):
        return BoolVal(True)

    def encode_null(self, pc):
        return self.cycle(0, pc) == 0

class ModifiedFunctionality(RecursiveDefinition):
    def __init__(self, rho, delta, fsa, nodes):
        self.rho = rho
        self.delta = delta
        self.fsa = fsa
        self.nodes = nodes

    def base(self, node, pc):
        return self.rho(node, pc) == self.delta(self.fsa.initial, node)

    def recurse(self, node, pc, n_to):
        return self.rho(node, pc) == self.delta(self.rho(n_to, pc), node)

    def auxiliary_def(self):
        query = BoolVal(True)
        for start, symbol, end in self.fsa.transitions:
            symbol = self.fsa.symbolAliases[symbol]
            query = And(query, self.delta(start, symbol) == end)

        return query

    def encode_null(self, pc):
        return self.rho(0, pc) == 0

class ComputeDestination(RecursiveDefinition):
    def __init__(self, dest, network, spec):
        self.dest = dest
        self.network = network
        self.spec = spec

    def base(self, node, pc):
        return self.dest(node, pc) == node

    def recurse(self, node, pc, n_to):
        return self.dest(node, pc) == self.dest(n_to, pc)

    def auxiliary_def(self):
        query = BoolVal(True)
        for pc in self.network.classes:
            for src in self.network.sources:
                # TODO: cleanup original_dest syntax, awkward ()[]
                srcname = self.network.node_strrep[src]
                pcobj = self.network.class_pcrep[pc]
                odname = pcobj.original_dest(self.network.concrete_network)[srcname]
                odint = self.network.node_intrep[odname]
                query = And(query,
                            self.dest(src, pc) == odint)

        return query

    def encode_null(self, pc):
        return self.dest(0, pc) == 0
