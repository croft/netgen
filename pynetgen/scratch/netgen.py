#!/usr/bin/env python

import argparse
import os
import shutil
import sys

import trie
import network
import spec
import synthesis
from topos import StanfordTopo, Internet2Topo, FattreeTopo, DiamondTopo
from network import HeaderField

TOPOS = { "stanford" : StanfordTopo,
          "internet2" : Internet2Topo,
          "fattree" : FattreeTopo,
          "diamond" : DiamondTopo
      }

# TODO: use one data structure for both
# TODO: add mask to flowtable
def ft2rules(loc, ft):
    rules = []
    for flow in ft:
        r = trie.Rule()
        r.ruleType = trie.Rule.FORWARDING

        if flow.src is not None:
            r.fieldValue[HeaderField.Index["NW_SRC"]] = network.ip2int(flow.src)
            r.fieldMask[HeaderField.Index["NW_SRC"]] = network.ip2int("255.255.255.255")

        if flow.dest is not None:
            r.fieldValue[HeaderField.Index["NW_DST"]] = network.ip2int(flow.dest)
            r.fieldMask[HeaderField.Index["NW_DST"]] = network.ip2int("255.255.255.255")

        r.priority = flow.priority

        # TODO: how to handle multiple next hops?
        r.nextHop = flow.nexthops[0]

        r.location = loc
        rules.append(r)

    return rules

# TODO: use one data structure for both
def graph2pc(i, fg):
    classes = []
    pc = network.PacketClass(idx=i)
    for name, link in fg.links.iteritems():
        if len(link) > 1:
            raise Exception("Don't know how to handle multiple links?")
        pc.edges[name] = link[0].rule.nextHop

    if len(pc.edges) == 0:
        return None

    return pc

def main():
    prog = os.path.basename(sys.argv[0])
    default_dest = "./output"
    default_spec = "./spec.txt"
    topos = "|".join(TOPOS.keys())

    desc = "NetGen dataplane change generator"
    usage = "{0} [options]\ntype {0} -h for details".format(prog)
    parser = argparse.ArgumentParser(description=desc, usage=usage)

    parser.add_argument("--topo", "-t", type=str, default=None, dest="topo",
                        help="Topology argument, choices: {0}".format(topos))
    parser.add_argument("--output", "-o", dest="dest",
                        default=default_dest,
                        help="output file destination (default: %s)" % default_dest)
    parser.add_argument("--spec", "-s", dest="spec",
                        default="spec.txt",
                        help="specification file (default: %s)" % default_spec)
    parser.add_argument("--debug", "-d", action="store_true", dest="debug",
                        default=False,
                        help="Debug output, files")

    args = parser.parse_args()

    if args.topo not in TOPOS.keys():
        print "Invalid topology {0}, must be one of: {1}".format(args.topo, topos)
        return

    if not os.path.isfile(args.spec):
        print "Specification file {0} does not exist!".format(args.spec)
        return

    # ----------------- TOPO GENERATION
    # TODO: better way of handling *params
    if args.topo == "fattree":
        topo = TOPOS[args.topo](4,1)
    else:
        topo = TOPOS[args.topo]()

    # For now/for debugging, still dump to data dir
    args.debug = True
    if args.debug:
        data_dir = "data"
        if os.path.exists(data_dir):
            shutil.rmtree(data_dir)

        os.makedirs(data_dir)
        topo.make_topofile(data_dir)
        topo.make_rocketfile(data_dir)
        topo.make_graph(data_dir)
        topo.make_configmap(data_dir)

    # ----------------- PACKET CLASS DISCOVERY
    mtrie = trie.MultilevelTrie()
    for switch in topo.switches.values():
        for rule in ft2rules(switch.name, switch.ft):
            mtrie.addRule(rule)

    classes = mtrie.getAllEquivalenceClasses()
    packetcls = {}
    for i in range(len(classes)):
        pktcls, pkttrie = classes[i]
        c = classes[i]
        graph = mtrie.getForwardingGraph(pkttrie, pktcls)
        pc = graph2pc(i, graph)
        if pc is not None:
            # TODO: no reason for this to be dict anymore?
            packetcls[i] = pc

    # TODO: redo constructor
    net = network.Network()
    net.classes = packetcls
    net.topo = topo

    # ----------------- SPEC PARSING
    s = spec.Specification(args.spec)
    s.parse(net, args.dest)

    solver = synthesis.Synthesizer(net, s)
    solver.solve()
if __name__ == "__main__":
    main()
