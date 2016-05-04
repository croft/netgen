#!/usr/bin/env python

import graphviz
import itertools
import os
import re

import dijkstra
import trie
from fields import HeaderField, ip2int

def pairwise(iterable):
    "s -> (s0,s1), (s1,s2), (s2, s3), ..."
    a, b = itertools.tee(iterable)
    next(b, None)
    return itertools.izip(a, b)

# TODO: use one data structure for both
# TODO: add mask to flowtable
def ft2rules(loc, ft):
    rules = []
    for flow in ft:
        r = trie.Rule()
        r.ruleType = trie.Rule.FORWARDING

        if flow.src is not None:
            r.fieldValue[HeaderField.Index["NW_SRC"]] = ip2int(flow.src)
            r.fieldMask[HeaderField.Index["NW_SRC"]] = ip2int("255.255.255.255")

        if flow.dest is not None:
            r.fieldValue[HeaderField.Index["NW_DST"]] = ip2int(flow.dest)
            r.fieldMask[HeaderField.Index["NW_DST"]] = ip2int("255.255.255.255")

        r.priority = flow.priority

        # TODO: how to handle multiple next hops?
        if len(flow.nexthops) > 1:
            raise Exception("Not implemented: multiple next hops")

        r.nextHop = flow.nexthops[0]
        r.location = loc
        rules.append(r)

    return rules

# TODO: use one data structure for both
def graph2pc(i, fg):
    classes = []
    pc = PacketClass(idx=i)
    for name, link in fg.links.iteritems():
        if len(link) > 1:
            raise Exception("Don't know yet how to handle multiple links?")
        pc.edges[name] = link[0].rule.nextHop

    if len(pc.edges) == 0:
        return None

    return pc

class PacketClass(object):
    def __init__(self, idx=None):
        self.idx = idx
        self.edges = {}

    def iteredges(self):
        e = []
        for src, dsts in self.edges.iteritems():
            if not isinstance(dsts, list):
                dsts = [dsts]
            for dst in dsts:
                e.append((src, dst))
        return e

    def original_dest(self, topo, sources=None):
        if sources is None:
            sources = []

        dest = {}
        egress = [e for e in topo.egresses
                  if e not in sources]
        for src in topo.switches.keys():
            if src in egress:
                dest[src] = src
                continue

            temp = src
            while temp in self.edges:
                temp = self.edges[temp]
                if temp in egress:
                    dest[src] = temp

        return dest

    def construct_strings(self):
        strings = []
        for key in self.edges.keys():
            s = []
            term = key
            while term in self.edges.keys():
                if term in s:
                    raise Exception("Loop in packet classes: {0}".format(s))
                s.append(term)
                term = self.edges[term]

            s.append(term)
            strings.append(" ".join(s))

        return strings

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "\n".join("{0} {1} {2}".format(self.idx, k,v) for k,v in self.edges.iteritems())

class NetworkConfig(object):
    def __init__(self, paths=None, egresses=None, pathfunc=None, params=None):
        self.egresses = egresses
        self.pathfunc = pathfunc
        self.paths = {}

        if egresses is None:
            self.egresses = []

        for src, dst, path in paths:
            if src not in self.paths:
                self.paths[src] = {}

            self.paths[src][dst] = path

        if len(paths) > 0 and pathfunc is not None:
            raise Exception("Path generator function and explicit paths "
                            "supplied!  Use only one!")

    def apply_config(self, topo_instance):
        if self.pathfunc is not None:
            self.paths = self.pathfunc(topo_instance)
        else:
            # look for paths with src,dst but no path specified
            for src in self.paths:
                for dst in self.paths[src]:
                    if self.paths[src][dst] is None:
                        self.paths[src][dst] = topo_instance.add_path(src, dst)

        for e in self.egresses:
            if e not in topo_instance.switches:
                raise Exception("Supplied egress not in topology: {0}"
                                .format(e))

        for src in self.paths:
            if src not in topo_instance.switches and \
               src not in topo_instance.hosts:
                raise Exception("Supplied path src not in topology: {0}"
                                .format(src))

            for dst in self.paths[src]:
                if dst not in topo_instance.switches and \
                   src not in topo_instance.hosts:
                    raise Exception("Supplied path dst not in topology: {0}"
                                    .format(dst))

                for node in self.paths[src][dst]:
                    if node not in topo_instance.switches and \
                       node not in topo_instance.hosts:
                        raise Exception("Node in path not in topology: {0}"
                                        .format(node))

        topo_instance.paths = self.paths
        topo_instance._egresses = self.egresses

class Node(object):
    def __init__(self, ip=None, mac=None, name=None):
        self.ip = ip
        self.mac = mac
        self.name = name

class Switch(Node):
    def __init__(self, ip=None, mac=None, name=None):
        self.ft = []
        super(Switch, self).__init__(ip, mac, name)

class Host(Node):
    def __init__(self, ip=None, mac=None, name=None):
        self.ft = []
        super(Host, self).__init__(ip, mac, name)

class FlowEntry(object):
    def __init__(self, dest, wildcard, location, nexthops, priority=1, src=None):
        if not isinstance(nexthops, list):
            nexthops = [nexthops]

        self.dest = dest
        self.src = src
        self.wildcard = wildcard
        self.location = location
        self.nexthops = nexthops
        self.priority = priority

    def __repr__(self):
        return str(self)

    def __str__(self):
        if len(self.nexthops) == 0:
            nhops = "-"
        else:
            nhops = ",".join(self.nexthops)

        return "- - {0} {1} {2} {3} - {4}".format(self.dest,
                                                  self.wildcard,
                                                  self.location,
                                                  nhops,
                                                  self.priority)

class Topology(object):
    def __init__(self):
        self.switches = {}
        self.hosts = {}
        self.edges = {}
        self.paths = {}
        self.distances = {}
        self._egresses = []
        self._classes = {}

    @property
    def strrepr(self):
        return {v: k for k,v in self.intrepr.items()}

    @property
    def intrepr(self):
        count = 1
        alias = {}
        for name in sorted(self.nodes.keys()):
            alias[name] = count
            count += 1

        return alias

    @property
    def nodes(self):
        n = self.switches.copy()
        n.update(self.hosts)
        return n

    @property
    def classes(self):
        if len(self._classes) == 0:
            self._compute_classes()
        return self._classes

    @property
    def egresses(self):
        # if manually defined
        if len(self._egresses) > 0:
            return self._egresses

        # otherwise, any switch with switch degree 1 or
        # any switch connected to a host
        e = []
        for s in self.switches.keys():
            if len(self.edges[s]) == 1:
                e.append(s)
                continue

            for neighbor in self.edges[s]:
                if neighbor in self.hosts:
                    e.append(s)
                    break

        return e

    def apply_config(self, config):
        config.apply_config(self)
        self.make_flowtable()

    def _compute_classes(self):
        mtrie = trie.MultilevelTrie()
        for switch in self.switches.values():
            for rule in ft2rules(switch.name, switch.ft):
                mtrie.addRule(rule)

        eqclasses = mtrie.getAllEquivalenceClasses()
        for ptrie, pclass in eqclasses:
            idx = len(self._classes) + 1
            graph = mtrie.getForwardingGraph(ptrie, pclass)
            pc = graph2pc(idx, graph)
            if pc is not None:
                self._classes[idx] = pc

    def _compute_distances(self):
        self.distances = {}
        for e1, e2 in self.iteredges():
            if e1 not in self.distances:
                self.distances[e1] = {}
            if e2 not in self.distances:
                self.distances[e2] = {}

            self.distances[e1][e2] = 2
            self.distances[e2][e1] = 2

    def match_classes(self, regex):
        matches = {}
        for p, pc in self.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    matches[p] = pc
                    break

        return matches

    def add_path(self, src, dst, path=None, bidirectional=False):
        # do we need to compute the path?
        if path is None:
            # has distances been initialized?
            if len(self.distances) == 0:
                self._compute_distances()

            path = dijkstra.shortestPath(self.distances, src, dst)

        if src not in self.paths.keys():
            self.paths[src] = {}

        self.paths[src][dst] = path

        if bidirectional:
            if dst not in self.paths.keys():
                self.paths[dst] = {}

            self.paths[dst][src] = path

        return path

    def alt_path(self, src, dst):
        if len(self.distances) == 0:
            self._compute_distances()

        distances = self.distances.copy()
        for k,v in pairwise(self.paths[src][dst]):
            distances[k][v] = distances[k][v] + 1

        path = dijkstra.shortestPath(self.distances, src, dst)
        self.add_path(src, dst, path)
        return path

    def write_debug_output(self, data_dir="output"):
        self.make_topofile(data_dir)
        self.make_rocketfile(data_dir)
        self.make_graph(data_dir)
        self.make_configmap(data_dir)

    def iteredges(self):
        e = []
        for src, dsts in self.edges.iteritems():
            if not isinstance(dsts, list):
                dsts = [dsts]
            for dst in dsts:
                e.append((src, dst))
        return e

    def make_configmap(self, dest_dir, mapfile="config.map"):
        out = []
        for switch in self.switches.keys():
            out.append("R R{0}\n".format(switch))
        with open(os.path.join(dest_dir, mapfile), 'w') as f:
            f.writelines(out)

    def make_topofile(self, dest_dir, topofile="topo.txt"):
        out = []
        written = []
        for src, dsts in self.edges.iteritems():
            for dst in dsts:
                if (dst,src) not in written:
                    out.append("{0} {1}\n".format(dst, src))
                    written.append((src, dst))

        with open(os.path.join(dest_dir, topofile), 'w') as f:
            f.writelines(out)

    def make_rocketfile(self, dest_dir):
        for sw in self.switches.values():
            with open(os.path.join(dest_dir, "R_" + sw.name), 'w') as f:
                f.write("\n".join([str(flow) for flow in sw.ft]))

    def make_graph(self, dest_dir, graphfile="topo.gv"):
        g = graphviz.Graph(format='svg')
        for node in self.hosts.keys() + self.edges.keys():
            g.node(node)

        added = []
        for src, dsts in self.edges.iteritems():
            for dst in dsts:
                if (src,dst) not in added:
                    g.edge(src, dst)
                    added.append((dst, src))

        g.render(os.path.join(dest_dir, graphfile))

    def switch_diff(self, subset, superset=None):
        if superset is None:
            superset = self.switches.keys()

        if not isinstance(subset, list):
            subset = [subset]

        return [s for s in superset if s not in subset]

    def make_flowtable(self):
        for src in self.paths.keys():
            for dst in self.paths[src].keys():
                path = self.paths[src][dst]
                src_ip = self.nodes[src].ip
                dst_ip = self.nodes[dst].ip
                wc = "255.255.255.255"

                # do we need to filter hosts?
                fwd_path = path
                if path[0] in self.hosts:
                    fwd_path = path[1:]

                if path[-1] in self.hosts:
                    fwd_path = fwd_path[:-1]

                for location, nexthop in pairwise(fwd_path):
                    flow = FlowEntry(dest=dst_ip,
                                     wildcard=wc,
                                     location=location,
                                     nexthops=nexthop,
                                     src=src_ip)
                    self.switches[location].ft.append(flow)
