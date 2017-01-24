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

import cli
import os
import subprocess
import sys
import tempfile
import socket
import dbcommands.lb_all_commands
from cli import lb_exception
from cli.completers import *
from cli.configutil import load_default_config
from cli.configutil import get_lb_deployment_home

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('server', help='lb server')

    server_subparsers = subparser.add_subparsers(title='server commands')

    if not cli.util.is_production():
        lb_logs = os.path.join(cli.util.get_lb_deployment_home(), 'logs', 'current')
        lb_server_log = os.path.join(lb_logs, 'lb-server.log')
        lb_server_pid = os.path.join(lb_logs, 'lb-server.pid')

        # Server start
        start_parser = server_subparsers.add_parser('start', help='start an lb-server')
        start_parser.add_argument('-p', '--port', dest='port', help='the port to connect to')
        start_parser.add_argument('--workspace-folder', help='the folder containing the workspace to connect to')

        # Note that it is okay for daemonize to have a default because
        # lb-server.config does not have this option.
        start_parser.add_argument('--daemonize', dest='daemonize', choices=['true', 'false'],
            help='start server in background mode (default: %(default)s)',
            default='true')

        # Note that it is important for this option to not have a
        # default because lb-server.config should be used.
        start_parser.add_argument('--systemd',
            dest='systemd',
            choices=['true', 'false'],
            help='if true, log to stderr, use systemd log levels (e.g. <3>) and omit timestamps (default: lb-server.config)')

        # Note that it is important for this option to not have a
        # default because lb-server.config should be used.
        start_parser.add_argument('--logfile',
            help='log file (default: lb-server.config)')

        # Note that it is okay for pidfile to have a default because
        # lb-server.config does not have this option.
        start_parser.add_argument('--pidfile',
            help='''when started as a daemon, write pid of daemon process in file
                    given as parameter. Similar to nohup x; echo $! > $pidfile.
                    The file will not be removed when the daemon finishes (default: %(default)s)''',
            default=lb_server_pid)

        start_parser.set_defaults(func=execute_server)

        # shutdown
        stop_parser = server_subparsers.add_parser('stop', help='stop a running lb-server')
        stop_parser.set_defaults(isAdmin=True)
        stop_parser.set_defaults(func=dbcommands.lb_all_commands.shutdown)

    # Server status
    status_parser = server_subparsers.add_parser('status', help='inquire status of running lb-server')
    status_parser.add_argument('--active', help='show active requests', action='store_true')
    status_parser.add_argument('--all', help='show all requests (active and queued)', action='store_true')
    status_parser.add_argument('--debug', help='show debug details', action='store_true')
    status_parser.add_argument('workspace', help='workspace(s) to be queried', action='store', nargs='*').completer = WorkspaceCompleter
    status_parser.set_defaults(isAdmin=True)
    status_parser.set_defaults(func=dbcommands.lb_all_commands.check_status)

    loglevel_parser = server_subparsers.add_parser('loglevel', help="change the server's default log level")
    loglevel_parser.add_argument('loglevel', help='log level to assign. ' + cli.util.get_log_levels(), action='store')
    loglevel_parser.set_defaults(isAdmin=True)
    loglevel_parser.set_defaults(func=dbcommands.lb_all_commands.server_loglevel)


def execute_server(args):
    lb_home = os.getenv('LOGICBLOX_HOME')
    command_line = [lb_home + '/bin/lb-server']
    if args.unixDomainSocket:
        command_line.extend(['--unix_domain_socket', args.unixDomainSocket])
    if args.port:
        command_line.extend(['--port', args.port])
    if args.workspace_folder:
        command_line.extend(['--workspaceFolder', args.workspace_folder])
    if args.systemd:
        command_line.extend(['--systemd', args.systemd])
    if args.logfile:
        command_line.extend(['--logfile', args.logfile])

    if args.daemonize == 'false':
        # Popen does not work with systemd; this works
        os.execvp(command_line[0], command_line)
    else:
        # This branch is only used when services are not managed in
        # systemd. The lb-server systemd unit sets daemonize to false.

        # Unfortunately we need to redirect the output of nohup
        # immediately, and cannot rely on the lb-server to redirect
        # its output to the log file, so we need to find the logfile
        # location from lb-server.config
        logfile = args.logfile
        if logfile == "-":
            raise lb_exception.LBCommandError("lb-server daemon cannot log to stdout when daemonize is true")
        if logfile == None:
            config = load_default_config('lb-server')
            logfile = config.get('logging', 'file')
            logfile = logfile.replace('$LB_DEPLOYMENT_HOME', get_lb_deployment_home())
           
        # To avoid setting up file descriptors, forking etc, we use
        # the existing systemd notify mechanism to let the daemon
        # process tell us when it's ready. This is necessary because
        # otherwise the callee might start using lb-server before it
        # is ready.

        # We cannot use mkstemp because the file should not exist. We
        # use mkdtemp to create a secure directory that cannot be
        # hijacked.
        tmpdir = tempfile.mkdtemp()
        # Unix domain sockets have a limit of 103. If the path is too long, try /tmp instead.
        if len(tmpdir) > 99:
            os.rmdir(tmpdir)
            tmpdir = tempfile.mkdtemp(dir='/tmp')
        sockname = os.path.join(tmpdir, 'sd')

        notify = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
        notify.bind(sockname)

        try:
            os.environ["NOTIFY_SOCKET"] = sockname
            command_line[:0] = ["nohup"]

            with open(logfile, 'a') as f:
                p = subprocess.Popen(command_line, stdout=f.fileno(), stderr=f.fileno(), close_fds=True)

            # We don't optimize for writing the pidfile only if
            # starting lb-server succeeded because a pidfile for a
            # non-existing pid is fine.
            with open(args.pidfile, 'w') as f:
                f.write('%d' % p.pid)

            # To avoid blocking unnecessarily long if there was a
            # failure, we loop 10 times and attempt to receive
            # notification. In every iteration, we check if the
            # process terminated (in which case it will surely never
            # notify us).

            # This terminate very quickly if we do receive a
            # notification, which is the case we want to optimize for
            notify.settimeout(1.0)
            timeout = 10
            for i in range(0, timeout):
                try:
                    msg = notify.recvfrom(1024)
                    if msg[0] == 'READY=1':
                        break;
                    else:
                        raise lb_exception.LBCommandError("lb-server daemon sent unexpected notification '%s'" % msg[0])
                except socket.timeout:
                    # Check if the process terminated, and if so report that.
                    p.poll()
                    if p.returncode is not None:
                        raise lb_exception.LBCommandError("lb-server daemon terminated with exit code %d. Check '%s'." % (p.returncode, logfile))

                    # Check if total timeout is exceeded. Still no
                    # notification. We don't know what is wrong with
                    # the process we launched. Return generic failure.
                    if i == timeout - 1:
                        raise lb_exception.LBCommandError("lb-server daemon did not confirm readiness within %d seconds. Check '%s'." %  (timeout, logfile))
        finally:
            # Ignore failures here to avoid that we obscure any
            # other exceptions in flight.
            try:
                notify.close()
            except:
                pass
            try:
                os.remove(sockname)
                os.rmdir(tmpdir)
            except:
                pass
