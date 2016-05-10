#!/usr/bin/env python

from runner import addPath
addPath()

import spec
import synthesis
from log import logger
from network import NetworkConfig
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo,
                   DiamondExtendedTopo, ThintreeTopo,
                   SosrTopo)

def run(name, topo, config, specstr):
    from profiling import ProfiledExecution
    pe = ProfiledExecution(name)
    pe.start()
    topo.apply_config(config)
    s = spec.Specification.parseString(topo, specstr)
    solver = synthesis.Synthesizer(topo, s)
    result = solver.solve()
    print result
    pe.stop()
    pe.print_summary()
    print "\n"

def test_fattree_perf():
    logger.setLogLevel("info")

    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s1 (N-s0)* od"
    run("fattree4,2", topo, config, specstr)

    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s0 .* => (N-s0)* s2 (N-s0)* od"
    run("fattree4,4", topo, config, specstr)

    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s0 .* => (N-s0)* s1 (N-s0)* od"
    run("fattree6,2", topo, config, specstr)

    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s0 .* => (N-s0)* s3 (N-s0)* od"
    run("fattree6,4", topo, config, specstr)

    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s0 .* => (N-s0)* s1 (N-s0)* od"
    run("fattree8,2", topo, config, specstr)

    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s0 .* => (N-s0)* s4 (N-s0)* od"
    run("fattree8,4", topo, config, specstr)

if __name__ == "__main__":
    test_fattree_perf()