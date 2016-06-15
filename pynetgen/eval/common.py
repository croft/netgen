#!/usr/bin/env python

import datetime
import os
import sys
import time

def addPath():
    # add ravel to path
    path = ""
    if 'PYTHONPATH' in os.environ:
        path = os.environ['PYTHONPATH']

    sys.path = path.split(':') + sys.path
    cwd = os.path.dirname(os.path.abspath(__file__))
    netgendir = os.path.normpath(os.path.join(cwd, ".."))
    sys.path.append(os.path.abspath(netgendir))

addPath()

import spec
import synthesis
import topos
from profiling import ProfiledExecution

CWD = os.path.dirname(os.path.realpath(__file__))
NUM_TRIALS = 10

#synthesizerType = synthesis.CppSynthesizer
synthesizerType = synthesis.CppCachingSynthesizer
#synthesizerType = synthesis.CppMTCachingSynthesizer
#synthesizerType = synthesis.PythonSynthesizer
#synthesizerType = synthesis.PythonCachingSynthesizer

# TODO:
# stanford drop
# rf fw immutable node

rf_specs = { "drop" : "not match(ip_src=a.b.c.d); 10.0.4.218: .* => .* drop",
             "avoid" : "not match(ip_src=a.b.c.d); 10.0.1.162: .* 10.0.1.153  .* => (N-10.0.1.153)* od",
             "fw" : "not match(ip_src=a.b.c.d); 10.0.0.166: .* => .* 10.0.0.154 .* od"
         }

stanford_specs = { "drop" : "not match(ip_src=a.b.c.d); yoza_rtr: .* => .* drop",
                   "avoid" : "not match(ip_src=a.b.c.d); yoza_rtr: .* => (N-yozb_rtr)* od",
                   "fw": "not match(ip_src=a.b.c.d); poza_rtr: .* => .* bbrb_rtr .* od NM:{bbrb_rtr}"
               }

# fattree_specs = { "drop" : "not match(ip_src=a.b.c.d); s132: .* => .* drop",
#                   "avoid" : "not match(ip_src=a.b.c.d); s132: .* s19 .* => .* s0 .* od",
#                   "fw" : "not match(ip_src=a.b.c.d); s132: .* s19 .* => (N-s19)* od"
#               }

fattree_specs = { "drop" : "not match(ip_src=a.b.c.d); s62: .* => .* drop od",
                  "avoid" : "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-s13)* od",
                  "fw" : "not match(ip_src=a.b.c.d); s62: .* s13 .* => (N-13)* s0 (N-13)* od"
              }

rf_dir = os.path.join(CWD, "/home/croft1/src/netgen/data_set/RocketFuel/AS-1755")
rf_cls = os.path.join(CWD, "/home/croft1/src/netgen/pynetgen/test/data/rf_classes")
sf_edges = os.path.join(CWD, "/home/croft1/src/netgen/pynetgen/test/data/stanford_topo.edges")
sf_cls = os.path.join(CWD, "/home/croft1/src/netgen/pynetgen/test/data/stanford_classes")

def topo_specs(toponame):
    if toponame == "rocketfuel":
        return rf_specs
    elif toponame == "stanford":
        return stanford_specs
    elif toponame == "fattree":
        return fattree_specs
    else:
        raise Exception("Unsupport topo type {0}".format(toponame))

def make_fattree(num_paths=0):
    #topo = topos.FattreeTopo(k=12)
    topo = topos.FattreeTopo(k=8)

    for i in range(len(topo.hosts)/2):
        if num_paths >= 0 and i >= num_paths:
            break

        h1 = topo.hosts.keys()[i]
        h2 = topo.hosts.keys()[len(topo.hosts.keys())-i-1]
        topo.add_path(h1, h2)

    topo.make_flowtable()
    topo.compute_classes()
    return topo

def topo_single_pc(toponame):
    if toponame == "rocketfuel":
        topo = topos.As1755Topo(no_ft=True, path=rf_dir)
        topo.deserialize_classes(rf_cls, start=1, limit=1)
    elif toponame == "stanford":
        topo = topos.StanfordTopo(no_ft=True)
        topo.load_edges(sf_edges)
        topo.deserialize_classes(sf_cls, start=1, limit=1)
    elif toponame == "fattree":
        topo = make_fattree(1)
    else:
        raise Exception("Unsupport topo type {0}".format(toponame))

    return topo

def topo_serialized_load(toponame):
    if toponame == "rocketfuel":
        topo = topos.As1755Topo(no_ft=True, path=rf_dir)
        topo.deserialize_classes("/home/croft1/src/gcc-next/datasets/as1755/classes")
    elif toponame == "stanford":
        topo = topos.StanfordTopo(no_ft=True)
        topo.load_edges(sf_edges)
        topo.deserialize_classes("/home/croft1/src/netgen/pynetgen/test/data/sclass")
    elif toponame == "fattree":
        topo = make_fattree()
    else:
        raise Exception("Unsupport topo type {0}".format(toponame))

    return topo

def topo_full_load(toponame):
    if toponame == "rocketfuel":
        topo = topos.As1755Topo(path=rf_dir)
        topo.compute_classes()
    elif toponame == "stanford":
        topo = topos.StanfordTopo()
        topo.compute_classes()
    elif toponame == "fattree":
        topo = make_fattree()
    else:
        raise Exception("Unsupport topo type {0}".format(toponame))

    return topo

def run_test(name, toponame, topofunc, specstr, destination, trial):
    print "*"*40
    print "Starting Trial:", trial
    print datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    print "*"*40

    # NOTE: not recording pc computation time
    topo = topofunc(toponame)

    elapsed = time.time()
    pe = ProfiledExecution(name)
    pe.start()
    s = spec.Specification.parseString(topo, specstr)
    matched = len(s.matched_classes.keys())

    if matched == 0:
        print "no matching classes!!!!!!!!!!"
        return

    solver = synthesizerType(topo, s)
    result = solver.solve()

    total_changes = 0
    print result
    for path in result.values():
        total_changes += len(path)

    # pprint.pprint(result)
    pe.stop()
    summary = pe.summary(separator=False)

    elapsed = round((time.time() - elapsed) * 1000, 3)

    if trial == 0:
        open(destination, 'w').close()

    with open(destination, 'a') as f:
        f.write("----------------------------\n")
        f.write("Trial: {0}\n".format(trial))
        f.write(summary)
        f.write("total_changes: {0}\n".format(total_changes))
        f.write("============================\n")
        f.write("Matched: {0}\n".format(matched))
        f.write("Elapsed: {0}\n".format(elapsed))
        f.write("\n")
