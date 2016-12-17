#!/usr/bin/env python

import json
import os
import sys
from networkx.readwrite import json_graph

path = ""
if 'PYTHONPATH' in os.environ:
    path = os.environ['PYTHONPATH']

sys.path = path.split(':') + sys.path
cwd = os.path.dirname(os.path.abspath(__file__))
updir = os.path.normpath(os.path.join(cwd, "..", "pynetgen"))
print updir
sys.path.append(os.path.abspath(updir))

import topos

for asnum in [1221, 1239, 1755, 2914, 3257, 3356, 3967, 4755, 6461, 7018]:
    topo = topos.RocketfuelTopo(asnum=asnum)
    print asnum, len(topo.nodes), len(list(topo.iteredges()))
    topo.make_graph(".", "rf_{0}".format(asnum))
    # d = json_graph.node_link_data(topo.to_networkx())
    # json.dump(d, open("force.json", "w+"))
    # break
