#!/usr/bin/env python

import argparse
import os
import sys

import trie
import network
import spec
import synthesis
from network import NetworkConfig
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo,
                   DiamondExtendedTopo, ThintreeTopo)

from network import HeaderField

TOPOS = { #"stanford" : StanfordTopo,
          #"internet2" : Internet2Topo,
          "fattree" : FattreeTopo,
          "diamond" : DiamondTopo,
          "diamondext" : DiamondExtendedTopo,
          "thintree" : ThintreeTopo
      }

CONFIGS = { "diamond" : NetworkConfig(egresses=['s4'],
                                      paths=[('s1', 's4',
                                              ['s1', 's2', 's4'])]),
            "diamondext" : NetworkConfig(egresses=['s6'],
                                         paths=[('s1', 's6',
                                                 ['s1', 's2', 's3', 's5', 's6'])]),
            "thintree" : NetworkConfig(egresses=['s10', 's11', 's1'],
                                       paths=[('s1', 's10',
                                               ['s1', 's2', 's4', 's8', 's10'])]),
            "fattree" : NetworkConfig(params=[4, 1],
                                      paths=[('h25', 'h34', None)])
        }

def main():
    prog = os.path.basename(sys.argv[0])
    default_dest = "./output"
    default_spec = "./specs/default.txt"
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

    tokens = args.topo.split(",")
    toponame = tokens[0]
    topoargs = []
    if len(tokens) > 1:
        topoargs = tokens[1:]

    if toponame not in TOPOS.keys():
        print "Invalid topology {0}, must be one of: {1}".format(toponame, topos)
        return

    if not os.path.isfile(args.spec):
        print "Specification file {0} does not exist!".format(args.spec)
        return

    topo = TOPOS[toponame](*topoargs)
    topo.apply_config(CONFIGS[toponame])

    s = spec.Specification(args.spec)
    s.parse(topo)

    if args.debug:
        if not os.path.isdir(args.dest):
            os.makedirs(args.dest)

        topo.write_debug_output(args.dest)
        s.write_debug_output(topo, args.dest)

    solver = synthesis.Synthesizer(topo, s)
    solver.solve()

if __name__ == "__main__":
    main()
