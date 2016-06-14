#!/usr/bin/env python

import os
import sys
import time
from common import *

addPath()
import spec
import synthesis
import topos

def evaluate(toponame, theory, encoding, dest):
    specs = topo_specs(toponame)
    for spectype, specstr in specs.iteritems():
        test_name = "encoding_{0}_{1}_{2}_{3}".format(toponame, theory, encoding, spectype)
        destfile = os.path.join(dest, test_name)
        for trial in range(NUM_TRIALS):
            run_test(test_name, toponame, topo_single_pc, specstr, destfile, trial)

if __name__ == "__main__":
    if len(sys.argv) != 5:
        print "{0} [topo] [theory] [encoding] [destination]".format(sys.argv[0])
        sys.exit(0)

    topo = sys.argv[1]
    theory = sys.argv[2]
    encoding = sys.argv[3]
    dest = sys.argv[4]
    evaluate(topo, theory, encoding, dest)
