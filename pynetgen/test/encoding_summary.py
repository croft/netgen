#!/usr/bin/env python

import os
import sys

def summarize(path, filt):
    result_files = [os.path.join(path, f) for f in os.listdir(path) if
                    os.path.isfile(os.path.join(path, f)) and
                    os.path.basename(f).startswith("result") and
                    f[-1] != "~" and
                    os.path.splitext(f)[1] == ".txt"]

    for r in result_files:
        testname = os.path.splitext(os.path.basename(r))[0].replace("result_", "")
        testname = testname.replace("results_", "")

        tokens = testname.split("_")
        assert len(tokens) == 2
        encoding_theory = tokens[0]
        encoding_type = tokens[1]

        cur_test = None

        print "\n"
        print "*"*35
        print "    ENCODING:", encoding_theory, encoding_type
        print "*"*35

        with open(r, 'r') as f:
            solve_times = {}
            query_times = {}
            totals = {}

            lines = f.readlines()
            for line in lines:
                line = line.strip()

                if line.startswith("----"):
                    topo = line.replace("-", "")
                    if topo:
                        cur_test = topo
                        solve_times[cur_test] = []
                        query_times[cur_test] = []

                if line.startswith("z3 solve"):
                    tokens = line.split(":")
                    latency = float(tokens[1].replace("ms", ""))
                    tokens = line.split("=")
                    k = int(tokens[1][0])
                    solve_times[cur_test].append((k, latency))

                if line.startswith("query"):
                    tokens = line.split(":")
                    latency = float(tokens[1].replace("ms", ""))
                    tokens = line.split("=")
                    k = int(tokens[1][0])
                    query_times[cur_test].append((k, latency))

                if line.startswith("Total"):
                    tokens = line.split(":")
                    latency = float(tokens[1].replace("ms", ""))
                    totals[cur_test] = latency


            for topo in sorted(solve_times.keys()):
                if filt is not None and filt not in topo:
                    continue

                print "-"*10, topo, "-"*10
                print "Query:", round(query_times[topo][-1][1] / 1000.0, 3), " secs"
                print "Solve:", round(solve_times[topo][-1][1] / 1000.0 / 60.0, 3), " mins"
                print "Total:", round(totals[topo] / 1000.0 / 60.0, 3), " mins"
                #print "{0}{1}{2}".format("-"*10, "-"*len(cur_test), "-"*10)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print "Usage: {0} [path] [filter]\n".format(sys.argv[0])
        print "   path: location of result files"
        print "   filter: string in form ft_size,k"
        print "\n   Example: {0} ~/ 16,2".format(sys.argv[0])
        sys.exit(0)

    filt = None
    if len(sys.argv) == 3:
        filt = sys.argv[2]
    
    summarize(sys.argv[1], filt)
