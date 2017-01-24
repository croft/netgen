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
import cli.util

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('libraries', help='search for LogicBlox libraries')
    subparser.set_defaults(func=execute_libraries)

    subparser.add_argument('libraries',
                           nargs='*',
                           help="libraries to locate")

    subparser.add_argument('--libpath',
                           help="library path to search")
    
    subparser.add_argument('--dependencies', '-d',
                           default=False,
                           action='store_true',
                           help="print the libraries upon which a library depends")

    subparser.add_argument('--quiet', '-q',
                           default=False,
                           action='store_true',
                           help="do not display any information. Used when simply querying the exit code")
    subparser

def execute_libraries(args):
    """
        Execute this command.
    """

    config = cli.util.load_default_config('lb-compiler')
    subenv = os.environ.copy()
    lbprefix = subenv.get('LOGICBLOX_HOME')

    java_args = ['java']
    if not cli.util.is_production():
      java_args.append('-ea')
    if config.has_option('GLOBAL', 'jvm_args'):
        java_args.extend(config.get('GLOBAL', 'jvm_args').split())
    java_args.append('-Djava.library.path='+lbprefix + '/lib')
    java_args.extend(['-cp', lbprefix + '/share/java/lb-compiler.jar'])
    java_args.append('com.logicblox.compiler.standalone.LibTool')

    if args.quiet:
      java_args.append('-q')
    if args.dependencies:
      java_args.append('--dependencies')
    if args.libpath != None:
      java_args.extend(['-libPath', args.libpath])
    if args.libraries != None:
      java_args.extend(args.libraries)

    os.execvpe('java', java_args, subenv)
