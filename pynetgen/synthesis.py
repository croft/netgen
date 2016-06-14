#!/usr/bin/env python

import abc
from z3 import *

import solver.cppsolver as cppsolver
from log import logger
from profiling import PerfCounter

class AbstractNetwork(object):
    def __init__(self, concrete_network, spec):
        self.concrete_network = concrete_network
        self.spec = spec
        self.fsa = self.spec.fsa
        classes = self.spec.matched_classes.values()

        self.edges = []
        self.rules = {}

        self.node_strrep = {}
        self.node_intrep = {}
        self.class_pcrep = {}

        # switch renaming
        for switch in sorted(self.concrete_network.switches.keys()):
            # TODO: clean this up
            alias = spec.fsa.symbolAliases[switch]
            self.node_strrep[alias] = switch
            self.node_intrep[switch] = alias

        for host in sorted(self.concrete_network.hosts.keys()):
            if host in spec.fsa.symbolAliases:
                alias = spec.fsa.symbolAliases[host]
            else:
                alias = len(self.node_intrep) + 1

            self.node_strrep[alias] = host
            self.node_intrep[host] = alias

        # packet class renaming
        idx = 1
        for pc in classes:
            self.class_pcrep[idx] = pc
            idx += 1

        for src, dst in self.concrete_network.iteredges():
            # end host or external node
            if src not in self.node_intrep.keys() or \
               dst not in self.node_intrep.keys():
                continue

            self.edges.append((self.node_intrep[src],
                               self.node_intrep[dst]))

        # add drop node
        for switch in self.node_strrep.keys():
            self.edges.append((switch, 0))

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

        # TODO: filter sources from sinks - is this correct?
        # XXX: we also need to add each packet class sink
        self._egresses = [self.node_intrep[s] for s in
                          self.concrete_network.egresses
                          if s not in spec.sources]

        if self.spec.drop:
            self._egresses.append(0)
            self.node_strrep[0] = "drop"
            self.node_intrep["drop"] = 0

        self.set_sinks(classes)

        self.immutables = [self.node_intrep[s] for s in spec.immutables]
                           # if s not in spec.sources and
                           # s not in self.concrete_network.egresses]

        # backup rules for reset()
        self.orig_rules = dict(self.rules)
        self.class_pcrep = dict(self.class_pcrep)

    def set_sinks(self, pcs):
        pc_sinks = set()
        for pc in pcs:
            for path in pc.powerset_paths(self.spec.sources,
                                          self.concrete_network.egresses):
                node = path[-1]
                if node in self.concrete_network.switches and \
                   node in self.concrete_network.egresses:
                    if self.node_intrep[node] not in pc_sinks:
                            pc_sinks.add(self.node_intrep[node])
                    break

        # remove dups
        #self.sinks = list(set(self.sinks + list(pc_sinks)))
        self.sinks = list(pc_sinks)
        if self.spec.drop:
            self.sinks.append(0)

    # reset absnet to a single packet class network
    def reset(self, pc):
        self.set_sinks([pc])
        self.rules = {}
        # set default value 0
        for switch in self.node_strrep.keys():
            self.rules[switch] = {}
            self.rules[switch][1] = 0

        for src, dst in pc.iteredges():
            src_int = self.node_intrep[src]
            dst_int = self.node_intrep[dst]
            self.rules[src_int][1] = dst_int

        self.class_pcrep = {}
        self.class_pcrep[1] = pc

    @property
    def nodes(self):
        return self.node_strrep.keys()

    @property
    def classes(self):
        return self.class_pcrep.keys()

class AbstractSynthesizer:
    __metaclass__ = abc.ABCMeta

    def __init__(self, network, spec):
        pass

    def solve(self):
        return

class CppSynthesizerBase(AbstractSynthesizer):
    def __init__(self, network, spec, solver_type):
        pc = PerfCounter("absnet creation")
        pc.start()
        self.solver_type = solver_type
        self.abstract_network = AbstractNetwork(network, spec)
        self.network = CppSynthesizer.convert_abstract_network(self.abstract_network)
        pc.stop()

    @classmethod
    def convert_abstract_network(cls, net):
        nodes = net.nodes
        sources = net.sources
        egresses = net.sinks
        immutables = net.immutables
        topo = net.edges
        switches = [net.node_intrep[n] for n in net.concrete_network.switches.keys()]

        classes = []
        for pcid, pc in net.class_pcrep.iteritems():
            # need to specify all possible pairs, set default to 0
            inactive = {}
            for node in nodes:
                inactive[node] = 0

            for m, n in pc.iteredges():
                inactive[net.node_intrep[m]] = 1
                classes.append((net.node_intrep[m], pcid, net.node_intrep[n]))

            for node in inactive.keys():
                if inactive[node] == 0:
                    classes.append((node, pcid, 0))

        fsa = []
        for s1, t, s2 in net.fsa.transitions:
            s1 = int(s1)
            s2 = int(s2)
            if t in net.node_intrep:
                fsa.append((s1, net.node_intrep[t], s2))
            else:
                fsa.append((s1, int(t), s2))

        symbols = net.fsa.symbolAliases.values()
        states = [int(s) for s in net.fsa.states]
        finals = [int(s) for s in net.fsa.final]
        initial = int(net.fsa.initial)
        dead = 0
        drop = 1 if net.spec.drop else 0

        return cppsolver.AbstractNetwork(nodes,
                                         switches,
                                         sources,
                                         egresses,
                                         immutables,
                                         topo,
                                         classes,
                                         fsa,
                                         states,
                                         symbols,
                                         finals,
                                         initial,
                                         dead,
                                         drop)

    def solve(self):
        solver = self.solver_type(self.network)
        result = solver.solve()

        paths = {}

        for p, f, t in result:
            if p not in paths:
                paths[p] = []

            # UF topo definition will solve n->drop, macro will do otherwise
            if int(f) not in self.abstract_network.node_strrep:
                f = 0
            if int(t) not in self.abstract_network.node_strrep:
                t = 0

            paths[p].append((self.abstract_network.node_strrep[int(f)],
                             self.abstract_network.node_strrep[int(t)]))

        for pc in solver.get_perf_counters():
            counter = PerfCounter("{0} k={1}".format(pc[1], pc[0]),
                                  pc[2])
            counter.report()

        # if len(paths) > 0:
        #     print "Model found:"

        # for p in paths.keys():
        #     print "   pktcls={0},  {1}".format(p, paths[p])

        return paths

class CppSynthesizer(CppSynthesizerBase):
    def  __init__(self, network, spec):
        super(CppSynthesizer, self).__init__(network,
                                             spec,
                                             cppsolver.DefaultSolver)

class CppCachingSynthesizer(CppSynthesizerBase):
    def  __init__(self, network, spec):
        super(CppCachingSynthesizer, self).__init__(network,
                                                    spec,
                                                    cppsolver.CachingSolver)

class CppMTCachingSynthesizer(CppSynthesizerBase):
    def  __init__(self, network, spec):
        super(CppMTCachingSynthesizer, self).__init__(network,
                                                    spec,
                                                    cppsolver.MultiThreadedCachingSolver)

class PythonSynthesizer(AbstractSynthesizer):
    def __init__(self, network, spec):
        pc = PerfCounter("absnet creation")
        pc.start()
        self.network = AbstractNetwork(network, spec)
        pc.stop()

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
        return [(self.network.node_strrep[int(str(f))],
                 self.network.node_strrep[int(str(t))])
                for (f, t) in links]

    def solve(self):
        set_option("pp.min-alias-size", 1000000)
        set_option("pp.max-depth", 1000000)

        for i in range(len(self.network.nodes)):
            logger.info("Starting phase %d", i+1)
            logger.debug("-------------------------------------------")
            logger.debug("        Phase: %d", i+1)
            logger.debug("-------------------------------------------")

            logger.debug("constructing query")
            query_pc = PerfCounter("query constr k={0}".format(i+1))
            query_pc.start()

            query = SmtQuery(self.fsa, self.network, i+1, self.spec)
            query.define_k_rules()
            query.define_immutability()
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
            query_pc.stop()
            solve_pc = PerfCounter("z3 solve k={0}".format(i+1))
            logger.debug("starting solution search")
            solve_pc.start()
            model = query.solve()
            solve_pc.stop()
            if model is not None:
                path = self.path_solution(model)
                logger.debug(model)
                logger.debug("Node mapping: %s", self.network.node_strrep)
                logger.info("Model found: %s", path)
                return path

class PythonCachingSynthesizer(PythonSynthesizer):
    def __init__(self, network, spec):
        super(PythonCachingSynthesizer, self).__init__(network, spec)
        self.prev_models = []
        self.results = {}

    # don't convert node ids to string representation
    def path_solution_raw(self, model):
        varnames = {}
        for g in model:
            if str(g)[0] == 'n':
                varnames[str(g)] = model[g]

        links = []
        for i in range(len(varnames.keys())/2):
            from_name = "n_{0}".format(i)
            to_name = "n1_{0}".format(i)
            links.append((varnames[from_name], varnames[to_name]))

        return links

    def solve(self):
        set_option("pp.min-alias-size", 1000000)
        set_option("pp.max-depth", 1000000)
        solves = 0
        cache_hits = 0
        cache_misses = 0

        classes = dict(self.network.class_pcrep)
        for pc in classes.keys():
            cls = classes[pc]
            self.network.reset(cls)
            is_cached = False
            result = None

            for model in self.prev_models:
                result = self._solve_with_prev(model)
                if result is not None:
                    cache_hits += 1
                    is_cached = True
                    break
                else:
                    cache_misses += 1

            if result is None:
                solves += 1
                result = self._solve()

            if result is None:
                print "No model found for packet class", cls.idx
            else:
                self.results[cls.idx] = [(self.network.node_strrep[int(str(f))],
                                          self.network.node_strrep[int(str(t))])
                                         for (f, t) in result]
                if not is_cached:
                    self.prev_models.append(result)

        print "\n\n-------------------------------------------"
        print "        FOUND MODELS"
        print "-------------------------------------------"
        for pc, result in self.results.iteritems():
            print "   ", pc, ":", result

        print "-------------------------------------------"
        print "   Total:", len(classes)
        print "   Solves:", solves
        print "   Cache Hits:", cache_hits
        print "   Cache Misses:", cache_misses
        print "-------------------------------------------"

        print "\n"

        # TODO
        return self.results

    def _solve(self):
        for i in range(len(self.network.nodes)):
            logger.info("Starting phase %d", i+1)
            logger.debug("-------------------------------------------")
            logger.debug("        Phase: %d", i+1)
            logger.debug("-------------------------------------------")

            logger.debug("constructing query")
            query_pc = PerfCounter("query constr k={0}".format(i+1))
            query_pc.start()

            query = SmtQuery(self.fsa, self.network, i+1, self.spec)
            query.define_k_rules()
            query.define_immutability()
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
            query_pc.stop()

            solve_pc = PerfCounter("z3 solve k={0}".format(i+1))
            logger.debug("starting solution search")
            solve_pc.start()
            model = query.solve()
            solve_pc.stop()

            if model is not None:
                path = self.path_solution_raw(model)
                logger.debug(model)
                logger.info("Model found")
                return path

    def _solve_with_prev(self, prev_model):
        set_option("pp.min-alias-size", 1000000)
        set_option("pp.max-depth", 1000000)
        i = len(prev_model) - 1

        logger.info("Starting check phase %d", i+1)
        logger.debug("-------------------------------------------")
        logger.debug("        Phase: %d", i+1)
        logger.debug("-------------------------------------------")

        logger.debug("constructing query")
        query_pc = PerfCounter("check query constr k={0}".format(i+1))
        query_pc.start()

        query = SmtQuery(self.fsa, self.network, i+1, self.spec)
        query.define_k_rules()
        query.define_existing_k_rules(prev_model)
        query.define_immutability()
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
        query_pc.stop()

        solve_pc = PerfCounter("check z3 k={0}".format(i+1))
        logger.debug("starting solution search")
        solve_pc.start()
        model = query.solve()
        solve_pc.stop()

        if model is not None:
            path = self.path_solution_raw(model)
            logger.debug(model)
            logger.info("Prev model SAT")
            return path
        else:
            logger.info("Prev model UNSAT")
            return None


# TODO: cleanup Synthesizer references, no default
# set default to Python
Synthesizer = PythonSynthesizer

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
        # logger.debug(self.solver.sexpr())
        if self.solver.check() == sat:
            return self.solver.model()
        else:
            return None

    def define_immutability(self):
        for i in range(self.k):
            for imm in self.network.immutables:
                self.query = And(self.query, self.n[i] != imm)

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

        # logger.debug(topostr)
        self.query = And(self.query, parse_smt2_string(topostr, ctx=main_ctx()))

    def define_existing_k_rules(self, prev_model):
        for i, (n_from, n_to)  in enumerate(prev_model):
            self.query = And(self.query, self.n[i] == n_from)
            self.query = And(self.query, self.n1[i] == n_to)

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
            query = And(query, self.dest(0, pc) == 0)
            srcnames = [self.network.node_strrep[src] for src in self.network.sources]
            sinknames = [self.network.node_strrep[src] for src in self.network.sinks]
            pcobj = self.network.class_pcrep[pc]

            if self.spec.drop:
                for src in self.network.sources:
                    query = And(query,
                                self.dest(src, pc) == 0)
            else:
                # TODO: cleanup original_dest syntax, awkward ()[]
                ods = pcobj.original_dest(self.network.concrete_network, srcnames, sinknames)

                for od_srcname, od_dstname in ods.iteritems():
                    srcint = self.network.node_intrep[od_srcname]
                    dstint = self.network.node_intrep[od_dstname]
                    query = And(query,
                                self.dest(srcint, pc) == dstint)

        return query

    def encode_null(self, pc):
        return self.dest(0, pc) == 0
