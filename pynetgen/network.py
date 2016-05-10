#!/usr/bin/env python

import graphviz
import itertools
import networkx
import os
import re

import trie
from log import logger
from fields import HeaderField, ip2int, int2ip
from profiling import PerfCounter

def pairwise(iterable):
    a, b = itertools.tee(iterable)
    next(b, None)
    return itertools.izip(a, b)

# TODO: use one data structure for both
# TODO: add mask to flowtable
def ft2rules(loc, ft):
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

        yield r

class PacketClass(object):
    def __init__(self, idx=None):
        self.idx = idx
        self.edges = {}
        self.graph = None
        self.rules = {}

    # TODO: one data structure for equivalence class/packet class
    @classmethod
    def fromForwardingGraph(cls, fg, idx=0):
        classes = []
        pc = PacketClass(idx=idx)
        pc.graph = fg

        for name, links in fg.links.iteritems():
            if name not in pc.edges:
                pc.edges[name] = []

            for link in links:
                pc.edges[name].append(link.rule.nextHop)

                f = FlowEntry.fromTrieRule(link.rule)
                if f.location not in pc.rules:
                    pc.rules[f.location] = {}

                for nexthop in f.nexthops:
                    pc.rules[f.location][nexthop] = f

        if len(pc.edges) == 0:
            return None

        return pc

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

        paths = self.powerset_paths()
        for src in topo.switches.keys():
            if src in egress:
                dest[src] = src
                continue

            src_paths = [p for p in paths if p[0] == src]
            dests = list(set([p[-1] for p in src_paths]))
            if len(dests) > 1:
                raise Exception("Can't handle multiple destinations yet")

            if len(dests) > 0:
                dest[src] = dests[0]

        return dest

    def powerset_paths(self):
        def rec_construct_paths(paths, path, node):
            if node in path:
                raise Exception("Loop in packet classes: {0}".format(path))

            if node not in self.edges:
                path.append(node)
                paths.append(path)
                return paths

            path.append(node)
            for nexthop in self.edges[node]:
                paths = rec_construct_paths(paths, list(path), nexthop)

            return paths

        paths = []
        for source in self.edges.keys():
            paths = rec_construct_paths(paths, [], source)

        return paths

    def construct_strings(self):
        return [" ".join(path) for path in self.powerset_paths()]

    def to_networkx(self):
        g = networkx.Graph()
        for m, n in self.iteredges():
            g.add_edge(m, n)

        return g

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "\n".join("{0} {1} {2}".format(self.idx, k,v)
                         for k,v in self.edges.iteredges())

class NetworkConfig(object):
    def __init__(self, paths=None, egresses=None, pathfunc=None, flowtable=None, params=None):
        self.egresses = egresses
        self.pathfunc = pathfunc
        self.flowtable = flowtable
        self.paths = {}

        if egresses is None:
            self.egresses = []

        if self.paths is not None:
            self.paths = paths

        if paths is not None and pathfunc is not None:
            raise Exception("Path generator function and explicit paths "
                            "supplied!  Use only one!")

    def _make_flowtable(self, topo):
        for location, src, dst, nexthop in self.flowtable:
            src_ip = None
            dst_ip = None
            wc = "255.255.255.255"

            if src is not None and src in topo.nodes.keys():
                src_ip = topo.nodes[src].ip

            if dst is not None and dst in topo.nodes.keys():
                dst_ip = topo.nodes[dst].ip

            flow = FlowEntry(dest=dst_ip,
                             wildcard=wc,
                             location=location,
                             nexthops=nexthop,
                             src=src_ip)

            topo.switches[location].ft.append(flow)

    def _make_paths(self, topo):
        if self.pathfunc is not None:
            self.paths = self.pathfunc(topo)

        for src, dst, path in self.paths:
            topo.add_path(src, dst, path)

    def apply_config(self, topo_instance):
        topo_instance._egresses = self.egresses
        if self.flowtable is not None:
            self._make_flowtable(topo_instance)
        else:
            self._make_paths(topo_instance)

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

    # TODO: one data structure for both rules
    @classmethod
    def fromTrieRule(cls, rule):
        # TODO support all fields?
        src = int2ip(rule.fieldValue[HeaderField.Index["NW_SRC"]])
        # TODO: add src mask?
        dest = int2ip(rule.fieldValue[HeaderField.Index["NW_DST"]])
        wc = int2ip(rule.fieldMask[HeaderField.Index["NW_DST"]])
        return FlowEntry(dest=dest,
                         src=src,
                         wildcard=wc,
                         nexthops=rule.nextHop,
                         priority=rule.priority,
                         location=rule.location)
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
        self.graph = None
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
            self.compute_classes()
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

    def build_from_graph(self, graph, hosts=None):
        if hosts is None:
            hosts = []

        self.graph = graph
        switches = [node for node in self.graph.nodes()
                    if node not in hosts]

        startip = ip2int("10.0.0.0")
        for name in switches:
            ip = startip + len(self.switches) + 1
            self.switches[name] = Switch(name=name,
                                         ip=int2ip(ip))

        startip = ip2int("10.1.0.0")
        for name in hosts:
            ip = startip + len(self.hosts) + 1
            self.hosts[name] = Host(name=name,
                                    ip=int2ip(ip))

        for e0, e1 in self.graph.edges():
            if e0 not in self.edges:
                self.edges[e0] = []
            if e1 not in self.edges:
                self.edges[e1] = []

            self.edges[e0].append(e1)
            self.edges[e1].append(e0)

    def compute_classes(self):
        pc = PerfCounter("pkt class")
        pc.start()
        mtrie = trie.MultilevelTrie()
        for switch in self.switches.values():
            for rule in ft2rules(switch.name, switch.ft):
                mtrie.addRule(rule)

        eqclasses = mtrie.getAllEquivalenceClasses()
        pc.stop()

        for ptrie, pclass in eqclasses:
            idx = len(self._classes) + 1
            graph = mtrie.getForwardingGraph(ptrie, pclass)
            pc = PacketClass.fromForwardingGraph(graph, idx)
            if pc is not None:
                self._classes[idx] = pc

    def match_classes(self, regex, sources=None):
        matches = {}
        for p, pc in self.classes.iteritems():
            for pathstr in pc.construct_strings():
                if re.match(regex, pathstr) is not None:
                    if sources is None:
                        matches[p] = pc
                        break
                    else:
                        for src in sources:
                            if src in pc.edges.keys():
                                matches[p] = pc
                                break
                    break

        return matches

    def add_path(self, src, dst, path=None, bidirectional=False):
        if path is None:
            path = networkx.shortest_path(self.graph, src, dst)
        else:
            # check nodes in path exist
            errnodes = [node for node in path if node not in self.nodes]
            if len(errnodes) > 0:
                raise Exception("Nodes do not exist in topology {0}"
                                .format(errnodes))

        if src not in self.paths.keys():
            self.paths[src] = {}

        self.paths[src][dst] = path

        if bidirectional:
            if dst not in self.paths.keys():
                self.paths[dst] = {}

            self.paths[dst][src] = path

        logger.debug("added path {0}".format(path))
        return path

    def add_multihop_path(self, hops, bidirectional=False):
        path = []
        for m, n in pairwise(hops):
            segment = networkx.shortest_path(self.graph, m, n)
            if len(path) > 0 and path[-1] == segment[0]:
                path += segment[1:]
            else:
                path += segment

        return self.add_path(hops[0], hops[-1], path, bidirectional)

    def iteredges(self):
        e = []
        for src, dsts in self.edges.iteritems():
            if not isinstance(dsts, list):
                dsts = [dsts]
            for dst in dsts:
                e.append((src, dst))
        return e

    def to_networkx(self):
        if self.graph is not None:
            return self.graph

        g = networkx.Graph()
        for m, n in self.iteredges():
            g.add_edge(m, n)

        return g

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

    def make_configmap(self, dest_dir, mapfile="config.map"):
        out = []
        for switch in self.switches.keys():
            out.append("R R{0}\n".format(switch))
        with open(os.path.join(dest_dir, mapfile), 'w') as f:
            f.writelines(out)

    def make_topofile(self, dest_dir, topofile="topo.txt"):
        out = []
        written = []
        for src, dst in self.edges.iteredges():
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
        for src, dsts in self.edges.iteredges():
            for dst in dsts:
                if (src,dst) not in added:
                    g.edge(src, dst)
                    added.append((dst, src))

        g.render(os.path.join(dest_dir, graphfile))

    def write_debug_output(self, data_dir="output"):
        self.make_topofile(data_dir)
        self.make_rocketfile(data_dir)
        self.make_graph(data_dir)
        self.make_configmap(data_dir)
