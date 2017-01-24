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

import os, sys

import cli
import cli.lb_exception
import cli.util
from cli.completers import *

# Require setting LB_WEBSERVER_HOME consistently.
candidates = []

## LB_WEBSERVER_HOME needs the following files:
## config/lb-web-server.config and lb-web-server.jar and other jar files in lib/java
lb_web_server_files = [
    'config/lb-web-server.config',
    'lib/java/lb-web-server.jar'
]

webserver_home = os.environ.get('LB_WEBSERVER_HOME')

WEBSERVER_IS_INSTALLED = False

if not webserver_home:
    # default error message (may change)
    ERROR_MSG = ("warning: lb-web-server installation is not known."
                 " Please load etc/profile.d/logicblox.sh or manually set LB_WEBSERVER_HOME.")
elif not os.path.isdir(webserver_home):
    ERROR_MSG = "warning: LB_WEBSERVER_HOME is set to '%s', but this directory does not exists" % os.environ.get('LB_WEBSERVER_HOME')
else:
    # This confirms that witness files exist
    verified_home = cli.util.find_home(candidates, lb_web_server_files, ['LB_WEBSERVER_HOME'])

    if not verified_home:
        ERROR_MSG = ("warning: LB_WEBSERVER_HOME is set to '%s', but this directory "
                     "does not appear to contain an lb-web distribution."  % os.environ.get('LB_WEBSERVER_HOME'))
    else:
        os.environ['LB_WEBSERVER_HOME'] = webserver_home

        sys.path.insert(0, '%s/lib/python' % webserver_home)
        try:
            # Need to import like this so that globals() will list all functions in the webserver module.
            # This may fail if the webserver_home does not point to a proper distribution (or to an older one)
            from web.webserver import *
            WEBSERVER_IS_INSTALLED = True

        except Exception,e:
            # sending some information about the exception in case this failed because of a syntax error
            ERROR_MSG = ("warning: LB_WEBSERVER_HOME is set to '%s', but this does not appear to be an "
                         "lb-web distribution.\n Exception: '%s'" % (os.environ.get('LB_WEBSERVER_HOME'),e))
            pass

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """

    # The main sub-command parser
    main_subparser = subparsers.add_parser(
        'web-server', help='logiQL web-server' + ' (not installed)' if not WEBSERVER_IS_INSTALLED else '',
        description=ERROR_MSG if not WEBSERVER_IS_INSTALLED else None)

    if WEBSERVER_IS_INSTALLED:
        add_webserver_commands(main_subparser)
    else:
        main_subparser.set_defaults(extra_func=no_webserver)

def no_webserver(args, extra, command_line):
    raise cli.lb_exception.LBServerOff(ERROR_MSG)

def add_webserver_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(title='web-server commands')

    # Use better formatter for commands, and use the standard of
    # invoking the function cmd_{subcommand}
    def add_command(cmd, help):
        p = more_subparsers.add_parser(cmd, help=help)
        fun = globals()['cmd_' + cmd.replace('-', '_')]
        p.set_defaults(func=fun)
        return p

    # Arguments for all subcommands related to proto credentials service
    def proto_credentials_arguments(p):
        p.add_argument('--url',
                       help='uRL of credentials service',
                       default="http://localhost:55183/admin/credentials")

    # Arguments for all subcommands related to delim users service
    def delim_users_arguments(p):
        p.add_argument('--url',
                       help='uRL of users service',
                       default="http://localhost:55183/admin/credentials/users")

    # Aguments for all subcommands that set properties of users.
    def set_user_arguments(p):
        p.add_argument('-c', '--create',
                       help="create user if no user exists for the given uid",
                       action="store_true")
        p.add_argument('username', help='username')

    if not cli.util.is_production():

        p = add_command('start', help="start the lb-web-server")
        p.add_argument('--daemonize', dest='daemonize', choices=['true', 'false'], default='false', help='start web-server in background mode (default: false)')
        p.add_argument('config',
                       nargs='?',
                       help='custom configuration file')

        p = add_command('stop', help="stop the lb-web-server")

        # Note that restart should take all arguments from start and stop
        p = add_command('restart', help="stop and start the lb-web-server")
        p.add_argument('--daemonize', dest='daemonize', choices=['true', 'false'], default='false', help='start web-server in background mode (default: false)')
        p.add_argument('config',
                       nargs='?',
                       help='custom configuration file')

    # TODO add wait option
    p = add_command('status', help="check status of lb-web-server")

    p = add_command('load', help="loads new configurations and handlers")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('-c', '--config', help="lb-web-server configuration file")
    group.add_argument('-j', '--jar', help="jar file")

    p = add_command('list', help="list's various attributes of the web-server.'")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('-H', '--handlers', action='store_true', help="list handlers installed in the server")
    group.add_argument('-s', '--services', action='store_true', help="list all services hosted in the web-server")
    group.add_argument('-e', '--endpoints', action='store_true', help="list endpoints configured in the server")
    group.add_argument('--handler', help="list configuration information about the handler with this id")

    p.add_argument('-v', '--verbose', action='store_true', dest="verbose", help="list full service configuration details")

    p = add_command('load-services', help="start or reload services of one workspace")
    p.add_argument('-w', '--workspace', help="workspace hosting services").completer = WorkspaceCompleter

    p = add_command('unload-services', help="stop services of one workspace")
    p.add_argument('-w', '--workspace', help="workspace hosting services").completer = WorkspaceCompleter

    p = add_command('enable-services', help="enable web-server services")
    # TODO add workspace option
    # TODO add group option
    p.add_argument('-p', '--prefix', required=True, help="the prefix of the service in the web-server")
    p.add_argument('-m', '--method', default='POST', help="the HTTP method (default is POST)")
    p.add_argument('-e', '--endpoint', help="the name of the endpoint for which the prefix is valid")

    p = add_command('disable-services', help="disable web-server services")

    # TODO add workspace option
    # TODO add group option
    p.add_argument('-p', '--prefix', required=True, help="the prefix of the service in the web-server")
    p.add_argument('-e', '--endpoint', help="the name of the endpoint for which the prefix is valid")
    p.add_argument('-m', '--method', default='POST', help="the HTTP method (default is POST)")
    p.add_argument('-s', '--status', default=503, help="the disabled status to be set on the service (default is 503: SERVICE UNAVAILABLE)")

    def log_categories():
        return ['messages', 'exception-details', 'http', 'profile', 'tdx']

    p = add_command('log', help='configure logging')
    p.add_argument('category',
                   choices=log_categories() + ['no-' + x for x in log_categories()],
                   nargs='+',
                   help='enable/disable logging for category')

    p = add_command('loglevel', help='configure database log level')
    p.add_argument('loglevel',
                   help='configure database log level (use only for debugging and performance analysis). ' + cli.util.get_log_levels())

    p = add_command('monitor', help='log assertions and retractions for predicates')
    p.add_argument('predname', nargs='*', help='predicate names to monitor')
    p.add_argument('-r', '--remove',action='store_true',dest="remove", help="remove the named predicates from list of monitored predicates")
    p.add_argument('-w', '--workspace', help="workspace in which to monitor")

    users_help = """pipe-delimited users file or S3 URL with required
                   column USER and optional columns EMAIL,
                   DEFAULT_LOCALE, ACTIVE, PASSWORD, and PUBLIC_KEY
                """

    p = add_command('import-users', help="import users delimited-file")
    delim_users_arguments(p)
    p.add_argument("file", nargs='?', help=users_help)
    p.add_argument("--full", help="fully replace existing data", action="store_true")

    p = add_command('export-users', help="export users delimited-file")
    delim_users_arguments(p)
    p.add_argument("file", nargs='?', help=users_help)

    p = add_command('set-password', help='set the password of a user using a credentials service')
    proto_credentials_arguments(p)
    set_user_arguments(p)

    p = add_command('reset-password', help='reset the password of a user (sends email to user)')
    p.add_argument('--url',
                   help='uRL of reset password service',
                   default="http://localhost:55183/user/reset-password")
    p.add_argument('username', help='username')

    p = add_command('confirm-reset-password', help='set the password of a user using a token')
    p.add_argument('--url',
                   help='uRL of confirm reset password service',
                   default="http://localhost:55183/user/confirm-reset-password")
    p.add_argument('token', help='token')

    p = add_command('set-public-key', help='set the public key of a user using a credentials service')
    proto_credentials_arguments(p)
    set_user_arguments(p)
    p.add_argument('filename', help='file contain public key (.pem)')

    p = add_command('set-user-active', help='set a user account to active/inactive')
    proto_credentials_arguments(p)
    set_user_arguments(p)
    p.add_argument('active', choices=['true', 'false'], metavar='ACTIVE', help='true or false')

    p = add_command('list-users', help='list users registered for a credentials service')
    proto_credentials_arguments(p)

    p = more_subparsers.add_parser('home-dir', help="print the directory used for LB_WEBSERVER_HOME")
    def print_home(args):
        print webserver_home
    p.set_defaults(func=print_home)
