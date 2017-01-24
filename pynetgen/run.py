#!/usr/bin/env python

import sys

import spec
import synthesis
from log import logger
from synthesis import PythonSynthesizer, CppSynthesizer, CppCachingSynthesizer
from network import NetworkConfig
from topos import (StanfordTopo, Internet2Topo,
                   FattreeTopo, DiamondTopo, LineTopo,
                   DiamondExtendedTopo, ThintreeTopo,
                   SosrTopo)

synthesizerType = CppCachingSynthesizer

def run(name, topo, config, specstr):
    from profiling import ProfiledExecution
    pe = ProfiledExecution(name)
    pe.start()
    topo.apply_config(config)
    s = spec.Specification.parseString(topo, specstr)
    solver = synthesizerType(topo, s)
    result = solver.solve()
    #print result
    pe.stop()
    pe.print_summary()
    print "\n"

def test_fattree_perf():
    logger.setLogLevel("info")

def testLineTopo():
    #line topo
    topo = LineTopo()
    config = NetworkConfig(paths=[('s1', 's5', ['s1', 's2', 's3', 's4', 's5'])]
                            )
    specstr = "not match(ip_src=a.b.c.d); s1: .* s3 .* => (N-s3)* s6 (N-s3)* od"
    print topo, config, specstr
    run("linetopo", topo, config, specstr)


def testForwardPath(self):
    # fattree 4 ------------------------------------------------------
    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None),
                                  ('h24', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s3 .* => (N-s3)* s2 (N-s3)* od"
    run("fattree4,2", topo, config, specstr)

    topo = FattreeTopo(k=4)
    config = NetworkConfig(paths=[('h25', 'h34', None),
                                  ('h24', 'h34', None)])
    specstr = "not match(ip_src=a.b.c.d); s14: .* s3 .* => (N-s3)* s0 (N-s3)* od"
    run("fattree4,4", topo, config, specstr)


    # fattree 6 ------------------------------------------------------
    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s2 .* => (N-s2)* s0 (N-s2)* od"
    run("fattree6,2", topo, config, specstr)

    topo = FattreeTopo(k=6)
    config = NetworkConfig(paths=[('h78', 'h98', None)])
    specstr = "not match(ip_src=a.b.c.d); s38: .* s2 .* => (N-s2)* s4 (N-s2)* od"
    run("fattree6,4", topo, config, specstr)


    # fattree 8 ------------------------------------------------------
    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-s13)* s12 (N-s13)* od"
    run("fattree8,2", topo, config, specstr)

    topo = FattreeTopo(k=8)
    config = NetworkConfig(paths=[('h138', 'h151', None)])
    specstr = "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-s13)* s0 (N-s13)* od"
    run("fattree8,4", topo, config, specstr)


    # fattree 10 -----------------------------------------------------
    topo = FattreeTopo(k=10)
    config = NetworkConfig(paths=[('h329', 'h250', None)])
    specstr = "not match(ip_src=a.b.c.d); s115: .* s22 .* => (N-s22)* s21 (N-s22)* od"
    run("fattree10,2", topo, config, specstr)

    topo = FattreeTopo(k=10)
    config = NetworkConfig(paths=[('h329', 'h250', None)])
    specstr = "not match(ip_src=a.b.c.d); s115: .* s22 .* => (N-s22)* s0 (N-s22)* od"
    run("fattree10,4", topo, config, specstr)


    # fattree 12 -----------------------------------------------------
    topo = FattreeTopo(k=12)
    config = NetworkConfig(paths=[('h334', 'h539', None)])
    specstr = "not match(ip_src=a.b.c.d); s133: .* s19 .* => (N-s19)* s20 (N-s19)* od"
    run("fattree12,2", topo, config, specstr)

    topo = FattreeTopo(k=12)
    config = NetworkConfig(paths=[('h334', 'h539', None)])
    specstr = "not match(ip_src=a.b.c.d); s133: .* s19 .* => (N-s19)* s0 (N-s19)* od"
    run("fattree12,4", topo, config, specstr)


    # fattree 14 -----------------------------------------------------
    topo = FattreeTopo(k=14)
    config = NetworkConfig(paths=[('h690', 'h587', None)])
    specstr = "not match(ip_src=a.b.c.d); s210: .* s19 .* => (N-s19)* s19 (N-s19)* od"
    run("fattree14,2", topo, config, specstr)

    topo = FattreeTopo(k=14)
    config = NetworkConfig(paths=[('h690', 'h587', None)])
    specstr = "not match(ip_src=a.b.c.d); s210: .* s19 .* => (N-s19)* s0 (N-s19)* od"
    run("fattree14,4", topo, config, specstr)


    # fattree 16 -----------------------------------------------------
    topo = FattreeTopo(k=16)
    config = NetworkConfig(paths=[('h920', 'h1270', None)])
    specstr = "not match(ip_src=a.b.c.d); s267: .* s31 .* => (N-s31)* s30 (N-s31)* od"
    run("fattree16,2", topo, config, specstr)

    topo = FattreeTopo(k=16)
    config = NetworkConfig(paths=[('h920', 'h1270', None)])
    specstr = "not match(ip_src=a.b.c.d); s267: .* s31 .* => (N-s31)* s0 (N-s31)* od"
    run("fattree16,4", topo, config, specstr)

def main():
    test_fattree_perf()

if __name__ == "__main__":
    main()
