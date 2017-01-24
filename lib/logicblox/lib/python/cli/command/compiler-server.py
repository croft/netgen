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

import os
from cli import util
from cli.util import load_default_config


def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('compiler-server', help='manage a LogicBlox compilation server')
    subparser.set_defaults(func=execute_daemon)
    add_daemon_commands(subparser)
    subparser

def add_daemon_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(title='daemon commands', dest="command")

    def add_command(cmd, help):
        p = more_subparsers.add_parser(cmd, help=help)
        p.add_argument('--port',
                       type=int,
                       help="port number to communicate with the compiler server.  Otherwise the default specified in 'lb-server.config' will be used")
        return p

    if not util.is_production(): 
      p = add_command('start', 'Start a LogicBlox compilation server')
      p.add_argument('--console',
                   default=False,
                   action='store_true',
                   help="open an administrative console for the compilation server")
      p = add_command('stop', 'Stop a running LogicBlox compilation server.')

    p = add_command('status', 'Ask a running LogicBlox compilation server for its status.')

def execute_daemon(args):
    """
        Execute this command.
    """

    config = load_default_config('lb-server')
    subenv = os.environ.copy()
    lbprefix = subenv.get('LOGICBLOX_HOME')

    if 'LB_DEPLOYMENT_HOME' not in subenv:
      subenv['LB_DEPLOYMENT_HOME']=subenv.get('HOME') + '/lb_deployment'

    java_args = ['java']
    if not util.is_production():
      java_args.append('-ea')
    if config.has_option('compiler', 'jvmArgs'):
        java_args.extend(config.get('compiler', 'jvmArgs').split())
    java_args.append('-Djava.library.path='+lbprefix + '/lib')
    java_args.append('-Djava.net.preferIPv4Stack=true')
    java_args.extend(['-jar', lbprefix + '/share/java/lb-compiler.jar'])

    if args.command == 'start':
      java_args.append('daemonStart')
      if args.port != None:
        java_args.extend(['-port', str(args.port)])
      if args.console == True:
        java_args.append('-console')

    if args.command == 'status':
      java_args.append('daemonStatus')
      if args.port != None:
        java_args.extend(['-port', str(args.port)])

    if args.command == 'stop':
      java_args.append('daemonStop')
      if args.port != None:
        java_args.extend(['-port', str(args.port)])

    os.execvpe('java', java_args, subenv)
