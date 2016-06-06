#!/usr/bin/env python

import sys

from runner import addPath
addPath()

import spec
import synthesis
from log import logger
from synthesis import PythonSynthesizer, CppSynthesizer
from network import NetworkConfig
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo,
                   DiamondExtendedTopo, ThintreeTopo,
                   SosrTopo)

synthesizerType = PythonSynthesizer

def run(name, topo, config, specstr):
    from profiling import ProfiledExecution
    pe = ProfiledExecution(name)
    pe.start()
    topo.apply_config(config)
    s = spec.Specification.parseString(topo, specstr)
    solver = synthesizerType(topo, s)
    result = solver.solve()
    print result
    pe.stop()
    pe.print_summary()
    print "\n"

def test_fattree_perf():
    logger.setLogLevel("info")

    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s3 .* => (N-s3)* s2 (N-s3)* od"
    run("fattree4,2", topo, config, specstr)

    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s3 .* => (N-s3)* s0 (N-s3)* od"
    run("fattree4,4", topo, config, specstr)

    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s2 .* => (N-s2)* s0 (N-s2)* od"
    run("fattree6,2", topo, config, specstr)

    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s2 .* => (N-s2)* s4 (N-s2)* od"
    run("fattree6,4", topo, config, specstr)

    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-s13)* s12 (N-s13)* od"
    run("fattree8,2", topo, config, specstr)

    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-s13)* s0 (N-s13)* od"
    run("fattree8,4", topo, config, specstr)

    topo = FattreeTopo(k=16)
    config = NetworkConfig(paths=[('h920', 'h1270', None)])
    specstr = "not match(ip_src=a.b.c.d); s267: .* s31 .* => (N-s31)* s30 (N-s31)* od"
    run("fattree16,2", topo, config, specstr)

    topo = FattreeTopo(k=16)
    config = NetworkConfig(paths=[('h920', 'h1270', None)])
    specstr = "not match(ip_src=a.b.c.d); s267: .* s31 .* => (N-s31)* s0 (N-s31)* od"
    run("fattree16,4", topo, config, specstr)

def main():
    global synthesizerType

    if len(sys.argv) > 1:
        if sys.argv[1].lower() in ["-h", "--help"]:
            print sys.argv[0], "usage:"
            print "  -h, --help   this help menu"
            print "  -c, --cpp    use cpp solver"
            print "  -p, --py     use python solver (default)"
        elif sys.argv[1].lower() in ["-c", "-cpp"]:
            synthesizerType = CppSynthesizer
    else:
        synthesizerType = PythonSynthesizer

    test_fattree_perf()

if __name__ == "__main__":
    main()
