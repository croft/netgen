"""
Copyright 2013 LogicBlox, Inc.

All rights reserved.

Redistribution and use in source and binary forms, with or 
without modification, are permitted provided that the following 
conditions are met:

Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer 
in the documentation and/or other materials provided with the 
distribution.

Neither the name of LogicBlox nor the names of its contributors 
may be used to endorse or promote products derived from this 
software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT 
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS 
"""
import sys
import os
import threading
import Queue
from cStringIO import StringIO
import time
import tempfile
import socket


import blox.connect.io

from cli import lb_exception
import lb_unit_common
from lb_unit_common import State


class ThreadTest(threading.Thread):


    def __init__(self, queue, error_list, count_dict, no_clean_up=False):
        threading.Thread.__init__(self)
        self.queue = queue
        self.error_list = error_list
        self.count_dict = count_dict
        self.no_clean_up = no_clean_up

    def run(self):
        """ takes Test object from the queue and runs it """

        ## importing this here so that we don't have to depend on readlines module
        ## for build, only for testing
        from interactive import lb_interactive_console

        while True:
            try:
                test_object = self.queue.get()

                # initialize interactive object
                interactive_ = lb_interactive_console.LbInteractive(
                                stdout=StringIO(),use_rawinput=False, dev=True)
                interactive_.set_current_directory(os.path.abspath(os.path.dirname(test_object.test_file)))
                # run setup
                if test_object.set_up:
                    lb_unit_common.run_file(test_object.set_up,
                            interactive_, test_object,
                            comment=test_object.test_file)

                # If setup does not generate errors, run test file
                if test_object.state == State.SUCCESS:
                    interactive_.clear_variables()
                    if test_object.concurrent:
                        raise lb_exception.LBCommandError("concurrent tests are no longer supported")
                    else:
                        lb_unit_common.run_file(test_object.test_file,
                                interactive_, test_object)

            finally:
                # run teardown
                if test_object.tear_down and not self.no_clean_up:
                    interactive_.clear_variables()
                    lb_unit_common.run_file(test_object.tear_down,
                            interactive_, test_object,
                            comment=test_object.test_file)
                if len(test_object.messages) != 0:
                    self.error_list.append(test_object.messages)

                self.count_dict[test_object.state] += 1
                test_object.test_report()
                self.queue.task_done()
                self.queue.count -= 1

class Test(object):

    default_set_up = None
    default_tear_down = None
    print_function = None
    print_progress = False
    print_time = False

    def __init__(self,test_file,set_up=None,tear_down=None,concurrent=False):
        self.test_file = test_file
        self.set_up = (set_up if set_up
                       != None else self.default_set_up)
        self.tear_down = (tear_down if tear_down
                          != None else self.default_tear_down)
        self.concurrent = concurrent

        self.testtimer = 0
        self.state = State.SUCCESS
        self.messages = []
        self.task_done = False

    def test_report(self):
        """print out report after test has finished"""

        if self.print_progress or self.print_time:
            testtime = ''
            if self.state == State.SUCCESS:
                testresult = '\tSuccess'
            elif self.state == State.FAILURE:
                testresult = '\tFailure'
            else:
                testresult = '\tError'
            if self.print_time:
                if self.state == State.SUCCESS:
                    testtime = ', ran in %.5f secs' % self.testtimer
                else:
                    testtime = ', did not complete'
            self.print_function.write('%s%s%s\n' % (self.test_file,
                    testresult, testtime))
            self.print_function.flush()
        else:
            self.print_function.write(self.state)
            self.print_function.flush()


def add_all_tests(args, test_queue):
    """given args, add all specified tests into test_queue"""

    if args.excludeTest == None:
        args.excludeTest = []
    if args.exclude == None:
        args.exclude = []
        
    # add suiteDirs
    if args.suiteDir != None:
        for suite_dir in args.suiteDir:
            add_dir(suite_dir, args, test_queue, recurse=True)

    # add suites
    if args.suite != None:
        for suite in args.suite:
            add_dir(suite, args, test_queue, recurse=False)

    # add individual tests
    if args.test != None:
        for test_file in args.test:
            test_file = test_file.rstrip('/')
            if os.path.exists(test_file) and test_file not in args.excludeTest:
                if os.path.isfile(test_file):
                    test_queue.put(test_to_test(test_file))
                    test_queue.count += 1
                elif os.path.basename(test_file).startswith("concurrent"):
                    test_queue.put(test_to_test(test_file, concurrent=True))
                    test_queue.count += 1
            else:
                print "Invalid file %s specified" % test_file

    # if none of the above conditions hold, find all suites in current directory
    if args.suiteDir == None and args.suite == None and args.test == None:
        add_dir(".", args, test_queue, recurse=True)


def add_dir(directory, args, test_queue, recurse=False):
    """add all tests from directory to test_queue"""
    # check directory exists
    if os.path.exists(directory) and os.path.isdir(directory):
        test_list = dir_to_tests(directory, 
                                 args.excludeTest, 
                                 args.exclude, 
                                 recurse, 
                                 args.noIgnore)
        for test in test_list:
            test_queue.put(test)
            test_queue.count += 1
    else:
        print "Invalid suite directory %s specified" % directory

def dir_to_tests(directory, excluded_tests, excluded_suites, recurse, no_ignore=False):
    """takes a directory, returns a list of Test objects"""
    tests = []
    # if this suite is somehow ignored, return empty list
    if ("suite.ignore" in os.listdir(directory) and not no_ignore) or directory in excluded_suites:
        return tests
    # loop through every file/dir in the directory
    for s in os.listdir(directory):
        spath = os.path.join(directory, s)
        # if directory
        if os.path.isdir(spath):
            if s.startswith("concurrent"):
                tests.append(test_to_test(spath, concurrent=True))
            elif spath not in excluded_suites and recurse:
                tests.extend(dir_to_tests(spath, 
                                          excluded_tests, 
                                          excluded_suites, 
                                          recurse, 
                                          no_ignore))
        # if file
        elif s.endswith(".lb") and not(s.startswith("setUp") or s.startswith("tearDown")):
            if spath not in excluded_tests:
                tests.append(test_to_test(spath))
    return tests

def test_to_test(test, concurrent=False):
    """given a test path, returns Test object"""
    dir_path = os.path.dirname(test)
    if not dir_path:
        dir_path = "."
    files = os.listdir(dir_path)
    set_up = None
    tear_down = None
    if "setUp.lb" in files:
        set_up = os.path.join(dir_path, "setUp.lb")
    if "tearDown.lb" in files:
        tear_down = os.path.join(dir_path, "tearDown.lb")
    return Test(test, set_up, tear_down, concurrent)



def get_line(file_path, line_number):
    with open(file_path) as f:
        for num, line in enumerate(f, 1):
            if num == line_number:
                return line.strip()

def print_summary(count_dict, error_list):
    run_total = count_dict[State.SUCCESS] + count_dict[State.ERROR] + count_dict[State.FAILURE]
    # if no tests ran
    if run_total == 0:
        print "\nNo tests run."
        return
    # print each error
    for i, test_result in enumerate(error_list):
        print "\n%i)" % (i+1),
        for j, error in enumerate(test_result):
            print "test: %s" % error.test_name,
            if error.comment:
                print "( %s )" % error.comment,
            print "\n(%s) line %i: \"%s\"" % (error.__class__.__name__, 
                                            error.line_num, 
                                            get_line(error.test_name, error.line_num))
            print "%s: %s" % (error.type, error.details)
    failure = "!!!FAILURES!!!\n" if count_dict[State.ERROR]+count_dict[State.FAILURE] != 0 else "OK\n"
    # results
    print "\n_________\n\n%sTest Results:\nRun:%i\tFailures:%i\tErrors:%i\n" % \
        (failure, run_total, count_dict[State.FAILURE], count_dict[State.ERROR])
    
def print_list(test_queue):
    """print out list of tests. used for the --list option"""
    curr_suite = None
    while not test_queue.empty():
        test = test_queue.get()
        suite_path = os.path.dirname(test.test_file)
        test_name = test.test_file.replace(suite_path, '')
        if suite_path != curr_suite:
            curr_suite = suite_path
            print '%s' % curr_suite
        print '\t%s' % test_name
    return

def main(args=None, supp_int_stdout=True, supp_int_stderr=True, supp_test_report=False):
    """
    runs set of tests given optional 'args' argument or takes from command line.
    optional 'suppress' argument for suppressing output from interactive REPL
    """
    # supp_int_stdout, supp_int_stderr suppress any output from running tests 
    # so that only test results are printed
    # by default they are True

    # supp_test_report suppresses output from results printed between tests 
    # such as progress and time, however the summary is still printed 
    # by default this is False

    #Check that lb services is started
    conn = blox.connect.io.Connection(False)
    try:
        conn.open()
    except Exception:
        raise lb_exception.LBServerOff()

    start_time = time.time()
    thread_count = 1
    test_queue = Queue.Queue()
    test_queue.count = 0
    error_list = []
    count_dict = {State.SUCCESS: 0, State.FAILURE: 0, State.ERROR: 0}
    stdout_orig = sys.stdout
    stderr_orig = sys.stderr
    Test.print_function = sys.stdout

    if args.defaultFixtures:
        # create default setup and teardown
        setup = tempfile.NamedTemporaryFile(delete=False)
        setup.write('create --unique')
        setup.close()

        teardown = tempfile.NamedTemporaryFile(delete=False)
        teardown.write('close --destroy')
        teardown.close()

        Test.default_set_up = setup.name
        Test.default_tear_down = teardown.name

    # find suites and tests from command line arguments
    add_all_tests(args, test_queue)

    # if list option, print tests and then return
    if args.list:
        print_list(test_queue)
        return

    # suppress stdout and stderr from interactive
    if supp_int_stdout:
        sys.stdout = StringIO()
    if supp_int_stderr:
        sys.stderr = StringIO()
    if supp_test_report:
        Test.print_function = StringIO()

    # set thread count
    if args.sequential:
        thread_count = 1
    elif args.threads != None:
        thread_count = args.threads

    # spawn a pool of threads, and pass them queue instance
    for i in range(int(thread_count)):
        thread = ThreadTest(test_queue, error_list, count_dict,
                       args.noCleanup)
        thread.setDaemon(True)
        thread.start()

    Test.print_progress = args.progress
    Test.print_time = args.time

    # wait on the queue until everything has been processed
    while test_queue.count != 0:
        try:
            conn.open()
            time.sleep(0.1)
        except socket.error:
            raise lb_exception.LBServerOff()

    Test.default_set_up = None
    Test.default_tear_down = None

    # restore stdout and stderr
    sys.stdout = stdout_orig
    sys.stderr = stderr_orig

    print_summary(count_dict, error_list)
    print 'Script Elapsed Time: %.5fs' % (time.time() - start_time)
    if error_list:
        raise lb_exception.LBCommandError("%s errors detected." % len(error_list))
