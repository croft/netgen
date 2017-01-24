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


from cli import lb_exception
from blox.connect import io,ConnectBlox_pb2


import StringIO
import errno, os, sys
from signal import *
import time
from configutil import *

# a module variable, set before blocking on a connectblox call
# used to interrupt the current transaction when receiving a signal

current_guid = None


def abort_transaction(guid):
    print("Requested interruption of transaction with GUID:%s"%guid)
    request = ConnectBlox_pb2.Request()
    request.cancel_requests.req_guid.append(guid)
    conn = Connection()
    conn.open()
    response = conn.call(request)
    if len(response.cancel_requests.unknown_guids)>0:
        print "Transaction already finished."
    else:
        print "Request accepted."

def sigint_handler(signal, frame):
        if current_guid is not None:
             abort_transaction(current_guid)
        sys.exit(1)


def set_sigint_handler():
    signal(SIGINT, sigint_handler)


#creates a handler which will display the timeout we are setting
def set_alarm_handler(timeout):
    def sigalarm_handler(signal,frame):
        print "Timeout( %sms) exceeded."%timeout
        if current_guid is not None:
            abort_transaction(current_guid)
            sys.exit(1)
    signal(SIGALRM, sigalarm_handler)




class Connection(io.Connection):
    """
        A connection to the lb server that throws a nice lb_exception if it cannot connect.
    """
    def open(self):
        try:
            return super(Connection, self).open()
        except IOError as e:
            if e.errno == errno.ECONNREFUSED:
                raise lb_exception.LBServerOff('lb-server: connection refused (most likely server is not running)')
            else:
                raise e

def is_production():
    """
      Report whether we are running in a production environment.  If we
      are not in a production environment, extra sanity checks may be
      enabled that could impact performance.
    """
    return 'LB_PRODUCTION_ENVIRONMENT' is os.environ


def check_lb_server_on():
    """
        Check that the lb server is on by opening and closing a connection to it.

        Note that if a connection is going to be used by a command, it is better to just
        open a connection, because it will check that the server is opened in the
        same way.
    """
    conn = Connection(False)
    conn.open()
    conn.close()


def which(command):
    """
    Check whether this command is found in the PATH environment variable and is executable.
    """
    return any(
        os.access(os.path.join(path, command), os.X_OK)
        for path in os.environ["PATH"].split(os.pathsep)
    )


def find_home(candidates, necessary_files, home_env_vars=None):
    """
    Find the home folder for a generic project.

    We look for the presence of certain files in a number of candidate folders.
    The first candidate folder that is tested is the one in pointed to
    by the any home_env_vars, if set. Checking progresses by looking at each
    candidate in candidates and returns the first that contains all
    necessary files.
    """

    if home_env_vars is not None:
        for home_env_var in home_env_vars:
            home_dir = os.environ.get(home_env_var)
            if home_dir:
                if has_necessary_files(home_dir, necessary_files):
                    return home_dir
                else:
                    # If an environment variable is set, then do not
                    # continue to scan for other stuff. It is a bad
                    # idea to continue to work in a misconfigured
                    # environment.
                    return None

    for candidate in candidates:
        candidate = os.path.join(os.path.dirname(__file__), candidate) if not os.path.isabs(candidate) else candidate
        if has_necessary_files(candidate, necessary_files):
            return os.path.normpath(candidate)

def has_necessary_files(folder, necessary_files):
    necessary_files = [os.path.join(folder, f) for f in necessary_files]
    return all(os.path.exists(f) for f in necessary_files)


def mkdirs(newdir):
    """
    Creates a directory at the specified location including all required parent
    directories if they do not exist. Unlike os.makedirs() it does not throw
    an error if the directory already exists.
    """
    try: os.makedirs(newdir)
    except OSError, err:
        # Reraise the error unless it's about an already existing directory
        if err.errno != errno.EEXIST or not os.path.isdir(newdir):
            raise


def setup_pid_file(pid_filename, pid, process=None):
    """
        Create a file pid_filename whose contents are this pid. Also set up a signal
        handler that will remove this file when the current process exisits with a
        signal.
    """
    with open(pid_filename, 'w') as f:
        f.write("%d" % pid)

    # function to cleanup pid file and terminate the process
    def cleanup(signal, frame):
        cleanup_pid_file(pid_filename)
        if process is not None:
            process.send_signal(SIGTERM)
        sys.exit(0)

    # register the cleanup function in case this process is terminated
    for sig in (SIGABRT, SIGILL, SIGINT, SIGSEGV, SIGTERM):
        signal(sig, cleanup)


def cleanup_pid_file(pid_filename):
    """
        Remove the pid file, if it exists.
    """
    if os.path.exists(pid_filename):
        #print 'removing pid file'
        os.remove(pid_filename)


def get_pid(pid_filename):
    """
        Extract the pid in this pid file.
    """
    with open(pid_filename) as pid_file:
        pid = pid_file.read()
        return pid


def check_process_running(pid_filename):
    """
        Check that the process identified by this pid_filename is running.

        The process is considered to be running iff:
           - the pid_filename exists, and contain a single integer identifying the process, and
           - the process responds to a signal 0, i.e., it is running.

        @return the pid of the process, if it is running; raise an exception otherwise.
    """
    # fail if the file does not exist
    pid = get_pid(pid_filename)
    # fail if the process does not exist
    check_pid_func(pid)()

    return pid


def communicate(process, pid_filename):
    """
        Communicate with this process until it terminates.

        This function will block until the process terminates. If the process
        terminates before the current process, this function will also remove
        the pid_filename file.

        @param process a process object (from subprocess.Popen)
        @param pid_filename the file that holds the pid of the process
    """
    # this will block until the process is over
    process.communicate()

    # if the other process terminates before the current process, cleanup the pid file
    cleanup_pid_file(pid_filename)


def wait_for(check_func, timeout, message, proc=None):
    """
        Waits until check_func does not throw an exception and proc is still alive.

        @param check_func a function without arguments that is used to check that wait is over.
        @param timeout number of seconds to wait until timeout.
        @param message a string with a single % for the timeout. This message is printed
                       every second that passes by.
        @param proc an optional process object (obtained e.g. from subprocess.Popen) for the process
               being monitored. If this process terminates before timeout, this method will throw an
               exception.
        @return True if check_func eventually returned True; False if timeout is reached.
    """
    passed = False
    while timeout > 0 and passed is False:
        try:
            check_func()
            passed = True
        except:
            if proc is not None and proc.poll() is not None and not proc.poll() == 0:
                raise Exception("process with PID %s terminated before timeout" % proc.pid)
            timeout = timeout - 1
            print message % timeout
            time.sleep(1)
    return passed


def check_pid_func(pid, running = True):
    """
        Returns a nullary function that checks that the process with pid is running (or not if running = False).
    """
    def check_pid():
        try:
            # this will return if the process running,
            # or throw an exception if it does not.
            os.kill(int(pid), 0)
            if not running:
                raise Exception("Process with PID %s is running" % pid)
        except Exception, e:
            if running:
                raise Exception("Process with PID %s is not running" % pid)
    return check_pid


def print_utf8(string):
   """
      Print to standard output using UTF-8 encoding.  Useful when printing
      strings which may contain non-ASCII characters.

      @param input string
   """
   encoded = string.encode('utf8')
   sys.stdout.write(encoded)


def get_log_levels():
    return "Valid levels are 'error', 'warning', 'info', 'perf', 'perf_detail' or 'debug'. A level may refer to a specific scope using @, and multiple specifications may be concatenated by colons. Examples: 'info', 'error@transport', 'info:debug@EvaluateRules'"
