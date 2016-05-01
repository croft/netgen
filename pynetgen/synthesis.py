#!/usr/bin/env python

import abc
from z3 import *

class Synthesizer(object):
    def __init__(self, network, spec):
        self.network = network
        self.spec = spec
        self.fsa = spec.fsa

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
        return [(self.network.topo.strrepr[int(str(f))],
                 self.network.topo.strrepr[int(str(t))])
                for (f, t) in links]

    def solve(self):
        #for i in range(5):
        for i in range(len(self.network.topo.switches.keys())):
            print "Phase", i+1

            attempt = SolveAttempt(self.fsa, self.network, i+1, self.spec)
            attempt.define_max_rules()
            attempt.delta_sat_topo()

            cycle = Function("cycle", IntSort(), IntSort(), IntSort())
            attempt.exec_recursion(Cyclicity(cycle))

            dest = Function("dest", IntSort(), IntSort(), IntSort())
            attempt.exec_recursion(ComputeDestination(dest, self.network, self.spec))

            rho = Function("rho", IntSort(), IntSort(), IntSort())
            delta = Function("delta", IntSort(), IntSort(), IntSort())
            attempt.exec_recursion(ModifiedFunctionality(rho,
                                                         delta,
                                                         self.fsa,
                                                         self.network.topo.switches.keys()))

            attempt.accept_automata(rho)
            model = attempt.solve()
            if model is not None:
                print "**********************************"
                print "*  MODEL FOUND"
                print "**********************************"
                path = self.path_solution(model)
                print path
                # print model[dest]
                # print model[rho]
                # print model[cycle]
                # print model[delta]
                break

class SolveAttempt(object):
    def __init__(self, fsa, network, k, spec):
        self.network = network
        self.fsa = fsa
        self.model = None
        self.n = []
        self.n1 = []
        self.pc = []
        self.max_changes = k
        self.spec = spec

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

    def delta_sat_topo(self):
        topostr = "(define-fun topology ((node_from Int) (node_to Int)) Bool \n"
        aliases = self.network.topo.intrepr

        lparens = 0
        for from_node, to_node in self.network.topo.iter_edges():
            from_int = aliases[from_node]
            to_int = aliases[to_node]
            topostr += " ( ite ( and ( = node_from {0} ) ( = node_to {1} )) true \n".format(from_int, to_int)
            lparens += 1

        topostr += " false"
        topostr += ")" * (lparens+1)
        topostr += "\n"

        for i in range(self.max_changes):
            topostr += "\n (declare-const {0} Int)".format(self.n[i])
            topostr += "\n (declare-const {0} Int)".format(self.n1[i])
            topostr += "\n (assert (topology {0} {1}))".format(self.n[i], self.n1[i])

        print topostr
        self.query = And(self.query, parse_smt2_string(topostr, ctx=main_ctx()))

    def define_max_rules(self):
        num_nodes = len(self.network.topo.switches.keys())

        for i in range(self.max_changes):
            n_str = "n_{0}".format(i)
            p_str = "p_{0}".format(i)
            n1_str = "n1_{0}".format(i)

            n_const = Const(n_str, IntSort())
            self.n.append(n_const)
            self.query = And(self.query, IntVal(0) < n_const)
            self.query = And(self.query, n_const <= IntVal(num_nodes))

            p_const = Const(p_str, IntSort())
            self.pc.append(p_const)
            self.query = And(self.query, IntVal(0) < p_const)
            self.query = And(self.query, p_const <= IntVal(len(self.network.classes.keys())))

            n1_const = Const(n1_str, IntSort())
            self.n1.append(n1_const)
            self.query = And(self.query, IntVal(0) < n1_const)
            self.query = And(self.query, n1_const <= IntVal(num_nodes))

    def exec_recursion(self, recfun):
        for pc in self.network.classes.values():
            self.query = And(self.query, recfun.auxiliary_def())
            self.query = And(self.query, recfun.encode_null(pc.idx))

            # convert to integer representation
            egress = [self.network.topo.intrepr[e] for e in self.network.topo.egresses()]
            aliases = self.network.topo.intrepr
            for nodename in self.network.topo.switches.keys():
                #if nodename not in pc.edges.keys():
                #    continue

                node = aliases[nodename]
                if node in egress:
                    self.query = And(self.query, recfun.base(node, pc.idx))
                else:
                    notnew = BoolVal(True)
                    for i in range(self.max_changes):
                        self.query = And(self.query, Implies(
                            And(IntVal(node) == self.n[i],
                                IntVal(pc.idx) == self.pc[i]),
                            recfun.change_rec(node, pc.idx, self.n1[i])))

                        notnew = And(notnew, Or(IntVal(node) != self.n[i],
                                                IntVal(pc.idx) != self.pc[i]))

                    # next hop in packet classes, as an integer
                    # TODO: can we remove this?
                    if nodename in pc.edges:
                        hop = pc.edges[nodename]
                        nexthop = aliases[hop]
                    else:
                        nexthop = 0

                    self.query = And(self.query, Implies(notnew,
                                                         recfun.default_rec(node,
                                                                            pc.idx,
                                                                            nexthop)))

    def accept_automata(self, rho):
        for pc in self.network.classes.values():
            sources = [self.network.topo.intrepr[s] for s in self.spec.sources]
            for src in sources:
                eachsrc = BoolVal(False)
                for final in self.fsa.final:
                    eachsrc = Or(eachsrc, rho(IntVal(src), IntVal(pc.idx)) == IntVal(final))

                self.query = And(self.query, eachsrc)

class RecursiveDefinition(object):
    __metaclass__ = abc.ABCMeta

    @abc.abstractmethod
    def base(self, i, j):
        return

    @abc.abstractmethod
    def change_rec(self, i, j, expr):
        return

    @abc.abstractmethod
    def default_rec(self, i, j, expr):
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
        return self.cycle(IntVal(node), IntVal(pc)) == IntVal(0)

    def change_rec(self, node, pc, n_to):
        return self.cycle(IntVal(node), IntVal(pc)) > self.cycle(n_to, IntVal(pc))

    def default_rec(self, node, pc, n_to):
        return self.cycle(IntVal(node), IntVal(pc)) > self.cycle(IntVal(n_to), IntVal(pc))

    def auxiliary_def(self):
        return BoolVal(True)

    def encode_null(self, pc):
        return self.cycle(IntVal(0), IntVal(pc)) == IntVal(0)

class ModifiedFunctionality(RecursiveDefinition):
    def __init__(self, rho, delta, fsa, nodes):
        self.rho = rho
        self.delta = delta
        self.fsa = fsa
        self.nodes = nodes

    def base(self, node, pc):
        return self.rho(IntVal(node), IntVal(pc)) == self.delta(IntVal(self.fsa.initial), IntVal(node))

    def change_rec(self, node, pc, n_to):
        return self.rho(IntVal(node), IntVal(pc)) == self.delta(self.rho(n_to, IntVal(pc)), IntVal(node))

    def default_rec(self, node, pc, n_to):
        return self.rho(IntVal(node), IntVal(pc)) == self.delta(self.rho(IntVal(n_to), IntVal(pc)), IntVal(node))

    def auxiliary_def(self):
        query = BoolVal(True)
        for start, symbol, end in self.fsa.transitions:
            symbol = self.fsa.symbolAliases[symbol]
            query = And(query, self.delta(IntVal(start), IntVal(symbol)) == IntVal(end))

        return query

    def encode_null(self, pc):
        return self.rho(IntVal(0), IntVal(pc)) == IntVal(0)

class ComputeDestination(RecursiveDefinition):
    def __init__(self, dest, network, spec):
        self.dest = dest
        self.network = network
        self.spec = spec

    def base(self, node, pc):
        return self.dest(IntVal(node), IntVal(pc)) == IntVal(node)

    def change_rec(self, node, pc, n_to):
        return self.dest(IntVal(node), IntVal(pc)) == self.dest(n_to, IntVal(pc))

    def default_rec(self, node, pc, n_to):
        return self.dest(IntVal(node), IntVal(pc)) == self.dest(IntVal(n_to), IntVal(pc))

    def auxiliary_def(self):
        query = BoolVal(True)
        for pc in self.network.classes.values():
            for src in self.spec.sources:
                # TODO: do we need to filter here?
                # if src in pc.edges.keys() + pc.edges.values():
                src_int = self.network.topo.intrepr[src]

                # TODO: cleanup original_dest syntax, awkward ()[]
                odname = pc.original_dest(self.network)[src]
                odint= self.network.topo.intrepr[odname]
                query = And(query,
                            self.dest(IntVal(src_int), IntVal(pc.idx)) == IntVal(odint))

        return query

    def encode_null(self, pc):
        return self.dest(IntVal(0), IntVal(pc)) == IntVal(0)
