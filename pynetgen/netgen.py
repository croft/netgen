#!/usr/bin/env python

import argparse
import os
import shutil
import sys

import trie
import network
import spec
import synthesis
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo,
                   DiamondExtendedTopo)
from network import HeaderField

TOPOS = { "stanford" : StanfordTopo,
          "internet2" : Internet2Topo,
          "fattree" : FattreeTopo,
          "diamond" : DiamondTopo,
          "diamondext" : DiamondExtendedTopo
      }

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

    # TODO: better way of handling *params
    if args.topo == "fattree":
        topo = TOPOS[args.topo](4,1)
    else:
        topo = TOPOS[args.topo]()

    net = network.Network(topo)

    s = spec.Specification(args.spec)
    s.parse(net, args.dest)

    if args.debug:
        topo.write_debug_output()
        s.write_debug_output(net)

    solver = synthesis.Synthesizer(net, s)
    solver.solve()

if __name__ == "__main__":
    main()
