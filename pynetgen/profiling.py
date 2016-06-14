import time
from collections import OrderedDict

from log import logger

_is_profiled = False
_execution = None

def enable_profiling():
    global _is_profiled
    _is_profiled = True

def disable_profiling():
    global _is_profiled
    _is_profiled = False

def is_profiled():
    return _is_profiled

class PerfCounter(object):
    "Store timing information for a single operation"

    def __init__(self, name, time_ms=None):
        """name: the name of the operation
           time_ms: the execution time of the operation, if already
           recorded"""
        self.name = name
        self.start_time = None
        self.time_ms = time_ms
        if self.time_ms is not None:
            self.time_ms = round(float(time_ms), 3)

    def start(self):
        "Start recording execution time of an operation"
        self.start_time = time.time()

    def stop(self):
        "Stop recording execution time of an operation"
        if self.start_time is not None:
            self.time_ms = round((time.time() - self.start_time) * 1000, 3)
            self.report()

        return self.time_ms

    def report(self):
        "Report the performance counter by adding it to the message queue"
        try:
            if is_profiled():
                _execution.report(self)
        except Exception, e:
            print e

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "{0}:{1}".format(self.name, self.time_ms)

class ProfiledExecution(object):
    "Start a new profiled execution and collect performance counters"

    def __init__(self, name):
        self.counters = []
        self.name = name
        self.start_time = None
        self.time_ms = None
        global _execution
        _execution = self


    def print_summary(self):
        "Print results of collected performance counters"
        print self.summary()

    def summary(self, separator=True):
        output = ""

        if len(self.counters) == 0:
            summ += "No performance counters found\n"
            return output

        agg = OrderedDict()
        summ = 0

        if separator:
            output += "{0}{1}{2}\n".format("-" * 15, self.name, "-" * 15)

        for counter in self.counters:
            summ += counter.time_ms

            if counter.name not in agg.keys():
                agg[counter.name] = (1, counter.time_ms)
            else:
                count,ms =  agg[counter.name]
                agg[counter.name] = (count + 1, ms + counter.time_ms)

        for counter, tup in agg.iteritems():
            output += "{0}({1}): {2}ms\n".format(counter, tup[0], tup[1])

        if separator:
            output += "-" * (30 + len(self.name))
            output += "\n"

        #print "Total: {0}ms".format(summ)
        output += "Total: {0}ms\n".format(self.time_ms)

        return output

    def start(self):
        "Enable profiling and start receiving performance counters"
        enable_profiling()
        self.start_time = time.time()

    def stop(self):
        "Disable profiling and stop receiving performance counters"
        self.time_ms = round((time.time() - self.start_time) * 1000, 3)

    def report(self, counter):
        """Callback for consuming performance counters
           obj: a PerfCounter object"""
        if counter is not None:
            self.counters.append(counter)
