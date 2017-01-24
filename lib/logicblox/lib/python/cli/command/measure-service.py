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
from cli import lb_exception

# default error message (may change)
ERROR_MSG = 'Measure service is not installed. Please install and set environment variable LB_MEASURE_SERVICE_HOME.'

MEASURE_SERVICE_IS_INSTALLED = False
measure_home = os.environ.get('LB_MEASURE_SERVICE_HOME')
if measure_home and os.path.exists(measure_home):
  MEASURE_SERVICE_IS_INSTALLED = True

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser(
        'measure-service', 
        add_help=MEASURE_SERVICE_IS_INSTALLED,
        help='interact with the measure service')
    
    if MEASURE_SERVICE_IS_INSTALLED:
      add_measure_commands(subparser)
      subparser.set_defaults(func=execute_measure)
    else:
      subparser.set_defaults(extra_func=no_measure_service)
    subparser

def no_measure_service(args, extra, command_line):
    raise lb_exception.LBServerOff(ERROR_MSG)    

def add_measure_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(title='measure service commands', dest="command")

    def add_command(cmd, help):
        p = more_subparsers.add_parser(cmd, help=help)
        p.add_argument('--uri', '-u', 
                       required=True,
                       help="URI for the measure service")
        return p
    p = add_command('admin', 'Send administrative requests.')
    p.add_argument('commands',
                   nargs='+',
                   help="Admin commands: refresh clear-cached-logic")

    p = add_command('install', 'Pre-install measure rules or queries.')
    p.add_argument('--rules', '-r', 
                   default=False,
                   action='store_true',
                   help="the input is in measure language rule format")
    p.add_argument('query-files',
                   nargs='+',
                   help="files containing measure queries")
  
    p = add_command('query', 'Query a measure service.')
    p.add_argument('query-files',
                   nargs='+',
                   help="files containing measure queries")
    p.add_argument('--in-format',
                   choices=['json', 'proto', 'text'],
                   default='proto',
                   help="select the format of the query files")
    p.add_argument('--out-format',
                   choices=['json', 'proto'],
                   default='proto',
                   help="select the format of the query output")
    
    p = add_command('repl', 'Open a CubiQL repl, execute a repl script, or evaluate an expression script.')
    p.add_argument('scripts',
                   nargs='*',
                   help="files containing CubiQL scripts")
    p.add_argument('--nocolor', '-n', 
                   default=False,
                   action='store_true',
                   help="disable color terminal output")
    p.add_argument('--commands',
                   default=False,
                   action='store_true',
                   help="treat each input file as containing interactive commands (rather than a CubiQL expression)")

def execute_measure(args):
    """
        Execute this command.
    """

    subenv = os.environ.copy()
    lbprefix = subenv.get('LOGICBLOX_HOME')
    measureprefix = subenv.get('LB_MEASURE_SERVICE_HOME')

    from web.webserver import prefix_deps_paths, lb_deps_paths

    java_args = ['java']
    if not util.is_production(): 
      java_args.append('-ea')
    
    classpath = ':'.join(prefix_deps_paths + lb_deps_paths +
                         [ measureprefix + '/lib/java/handlers/lb-measure-service.jar',
                           measureprefix + '/lib/java/jline-2.12.1.jar'
                         ])
    java_args.extend(['-cp', classpath])
    
    if args.command == 'admin':
      java_args.append('com.logicblox.bloxweb.measure.AdminTool')
      java_args.extend(['-u', args.uri])
      java_args.extend(getattr(args, 'commands'))

    if args.command == 'install':
      java_args.append('com.logicblox.bloxweb.measure.Installer')
      java_args.extend(['-u', args.uri])
      if args.rules != None: 
        java_args.append('--rules')
      java_args.extend(getattr(args, 'query-files'))

    if args.command == 'query':
      java_args.append('com.logicblox.bloxweb.measure.QueryTool')
      java_args.extend(['-u', args.uri])
      if args.in_format != None: 
        java_args.extend(['-inputFormat', args.in_format])
      if args.out_format != None: 
        java_args.extend(['-outputFormat', args.out_format])
      java_args.extend(getattr(args, 'query-files'))
    
    if args.command == 'repl':
      java_args.append('com.logicblox.bloxweb.measure.repl.ReplTool')
      if args.nocolor:
        java_args.append('--nocolor')
      if args.commands:
        java_args.append('--commands')
      java_args.extend(['-u', args.uri])
      java_args.extend(getattr(args, 'scripts'))

    os.execvpe('java', java_args, subenv)
