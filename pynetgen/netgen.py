#!/usr/bin/env python

import argparse
import os
import sys

import spec
import synthesis
from log import logger
from network import NetworkConfig
from profiling import ProfiledExecution
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo,
                   DiamondExtendedTopo, ThintreeTopo,
                   SosrTopo, As1755Topo, DiamondClusterTopo)

TOPOS = { "stanford" : StanfordTopo,
          "internet2" : Internet2Topo,
          "fattree" : FattreeTopo,
          "diamond" : DiamondTopo,
          "line"    : LineTopo,
          "diamondext" : DiamondExtendedTopo,
          "thintree" : ThintreeTopo,
          "sosr" : SosrTopo,
          "as1755" : As1755Topo,
          "cluster" : DiamondClusterTopo
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
            "fattree" : NetworkConfig(paths=[('h25', 'h34', ['h25', 's14', 's6', 's0',
                                                             's10', 's19', 'h34'])]),
            "sosr" : NetworkConfig(egresses=['Z'],
                                   flowtable=[('A', '10.0.1.1', 'Z', 'F1'),
                                              ('B', '10.0.1.1', 'Z', 'F1'),
                                              ('C', '10.0.1.1', 'Z', 'F1'),
                                              ('F1', '10.0.1.1', 'Z', 'X'),
                                              ('X', '10.0.1.1', 'Z', 'Z'),
                                              ('F2', '10.0.1.1', 'Z', 'Y')]),
            "cluster" : NetworkConfig(egresses=['Dst'],
                                      paths=[('Src', 'Dst',
                                              ['Src', 's14', 'Core', 's15', 'Dst'])])
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
                        help="Save files (packet classes, automata) for debugging")
    parser.add_argument("--verbose", "-v", dest="verbose", action="store_true",
                        help="Enable verbose log output")
    parser.add_argument("--profile", "-p", dest="profile", action="store_true",
                        help="Enable performance profiling")

    args = parser.parse_args()

    if args.verbose:
        logger.setLogLevel("debug")
    else:
        logger.setLogLevel("info")

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

    if args.profile:
        pe = ProfiledExecution("netgen")
        pe.start()

    topo = TOPOS[toponame](*topoargs)
    if toponame in CONFIGS:
        topo.apply_config(CONFIGS[toponame])

    # TODO: new way to load classes
    # if toponame == "as1755":
    #     topo.load_cached_classes("../data_set/RocketFuel/classes")

    s = spec.Specification.parseFile(topo, args.spec)

    if args.debug:
        if not os.path.isdir(args.dest):
            os.makedirs(args.dest)

        topo.write_debug_output(args.dest)
        s.write_debug_output(topo, args.dest)

    solver = synthesis.Synthesizer(topo, s)
    solver.solve()

    if args.profile:
        pe.stop()
        pe.print_summary()

if __name__ == "__main__":
    main()
