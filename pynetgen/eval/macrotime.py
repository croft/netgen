#!/usr/bin/env python

import os
import sys
import time
from common import *

addPath()
import spec
import synthesis
import topos

def evaluate(toponame, dest)
    specs = topo_specs(toponame)
    for spectype, specstr in specs.iteritems():
        test_name = "time_{0}_{3}".format(toponame, spectype)
        destfile = os.path.join(dest, test_name)
        for trial in range(NUM_TRIALS):
            run_test(toponame, test_name, specstr, destfile, trial)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print "{0} [topo] [destination]".format(sys.argv[0])
        sys.exit(0)

    topo = sys.argv[1]
    dest = sys.argv[2]
    evaluate(topo, dest)
