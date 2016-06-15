#!/usr/bin/env python

import os
import pprint
import re
import sys

import numpy

class TestResult(object):
    def __init__(self, name):
        self.trial = 0
        self.matches = 0
        self.num_classes = 0
        self.elapsed = 0.0
        self.total_time = 0.0
        self.match_time = 0.0
        self.query_constr = 0.0
        self.absnet_creation = 0.0
        self.z3_solve = 0.0
        self.cache_hits = 0
        self.cache_misses = 0
        self.max_k = 0
        self.total_k = 0
        self.test_name = name

    def parse_line(self, line):
        tokens = line.split(":")
        if len(tokens) < 2:
            return

        label = tokens[0]
        value = float(tokens[1].replace("ms", ""))

        if label.startswith("Trial"):
            self.trial = int(value)
        elif label.startswith("match_classes"):
            self.match_time += value
        elif label.startswith("absnet_creation"):
            self.absnet_creation += value
        elif label.startswith("query constr"):
            self.query_constr += value
        elif label.startswith("check query constr"):
            self.query_constr += value
        elif label.startswith("z3 solve"):
            self.z3_solve += value
        elif label.startswith("check z3"):
            self.z3_solve += value
        elif label.startswith("cache_hits"):
            self.cache_hits = int(value)
        elif label.startswith("cache_misses"):
            self.cache_misses = int(value)
        elif label.startswith("Matched:"):
            self.matches = int(value)
        elif label.startswith("total_classes"):
            self.num_classes = int(value)
        elif label.startswith("total_changes"):
            self.total_k = int(value)
        elif label.startswith("Elapsed"):
            self.elapsed = value
        elif label.startswith("Total"):
            self.total_time = value

        m = re.search(r"k=(\d+)\(", line)
        if m is not None:
            k = m.group(1)
            if k > self.max_k:
                self.max_k = k

def summarize_encodings(results):
    fixed_spec = "fw"

    # topo -> theory -> encoding -> trials
    types = {}

    for result in results:
        tokens = result.test_name.split("_")
        topo = tokens[1].strip()
        theory = tokens[2].strip()
        encoding = tokens[3].strip()
        spectype = tokens[4].strip()

        # we're only analyzing one type of spec
        if spectype != fixed_spec:
            continue

        if topo not in types:
            types[topo] = {}
        if theory not in types[topo]:
            types[topo][theory] = {}
        if encoding not in types[topo][theory]:
            types[topo][theory][encoding] = []

        types[topo][theory][encoding].append(result)

    # output format: topo lia+uf lia+macro bv+uf bv+macro
    for topo in types.keys():
        output = "topo lia+uf lia+macro bv+uf bv+macro k\n"
        output += topo + " "

        # order lia, bf
        for theory in sorted(types[topo].keys(), reverse=True):

            # order uf, macro
            for encoding in sorted(types[topo][theory].keys(), reverse=True):

                elapseds = [e.elapsed for e in types[topo][theory][encoding]]
                q25, median, q75 = numpy.percentile(elapseds, [25, 50, 75])
                q25 = (q25 / 1000.0)# / 60.0
                q75 = (q75 / 1000.0)# / 60.0
                median = (median / 1000.0)# / 60.0
                output += "{0} {1} {2}  ".format(median, q25, q75)

        output += "\n"
        with open("encodings_{0}.dat".format(topo), 'w') as f:
            f.write(output)

def summarize_macrotime(path, name):
    pass

def parse_perf_counters(path, name):
    f = open(path, 'r')
    results = []
    t = None
    for line in f.readlines():
        if line.startswith("---"):
            if t is not None:
                results.append(t)
            t = TestResult(name)
            continue

        t.parse_line(line)

    results.append(t)
    f.close()
    return results

def parse(dired):
    files = [os.path.join(dired, f) for f in
             os.listdir(dired) if
             f[-1] != "~"]

    results = []
    for fpath in files:
        fname = os.path.basename(fpath)
        test_type = fname.split("_")[0]
        results.extend(parse_perf_counters(fpath, fname))

    summarizer[test_type](results)

summarizer = { "encoding" : summarize_encodings,
               "macrotime" : summarize_macrotime,
           }

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print "{0} [result dir]".format(sys.argv[0])
        sys.exit(0)

    parse(sys.argv[1])
