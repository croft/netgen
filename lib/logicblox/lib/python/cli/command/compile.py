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
from cli.util import load_global_config
from cli import lb_exception

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('compile', help='compile LogicBlox logic')
    subparser.set_defaults(func=execute_compile)
    add_compile_commands(subparser)
    subparser

def add_compile_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(
      title='compile commands', dest="command", description='compile LogiQL source files and projects')

    def add_command(cmd, help):
        p = more_subparsers.add_parser(cmd, help=help)
        return p

    p = add_command('file', 'Compile an individual file for testing.')
    p.add_argument('--serialize', 
                   help="serialize binary protobuf ouput to a file. (Requires --output-format proto.)")
    p.add_argument('--out-format',
                   choices=['logiql', 'proto', 'xml'],
                   default='logiql',
                   help="select the format for pretty-printing the compiled output")
    p.add_argument('--stage',
                   choices=['initial', 'final'],
                   default='final',
                   help="select the transaction stage used when compiling")
    p.add_argument('--lifetime',
                   choices=['transaction', 'database'],
                   default='database',
                   help="select the logic lifetime used when compiling")
    p.add_argument('logic-file',
                   nargs='?',
                   help="logic (.logic) file to compile")
  
    p = add_command('project', 'Compile a LogicBlox project.')
    p.add_argument('--out-dir', 
                   help="directory to place compiled binaries")
    p.add_argument('--libpath',
                   help="library path to search") 
    p.add_argument('--progress', 
                   default=False,
                   action='store_true',
                   help="print the progress of separate compilation")
    p.add_argument('--explain', 
                   default=False,
                   action='store_true',
                   help="print explanations as to why certain compilation decisions were made")
    p.add_argument('--clean', 
                   default=False,
                   action='store_true',
                   help="separately compile all files in project from scratch")
    p.add_argument('--max-problems',
                   default=50,
                   type=int,
                   help="the maximum number of compilations errors and warnings to print") 
    p.add_argument('project-file',
                   help="project (.project) file to compile")

def execute_compile(args):
    """
        Execute this command.
    """

    config = load_global_config('lb-compiler')
    subenv = os.environ.copy()
    lbprefix = subenv.get('LOGICBLOX_HOME')

    java_args = ['java']
    if not util.is_production(): 
      java_args.append('-ea')
    if config.has_option('GLOBAL', 'jvm_args'):
        java_args.extend(config.get('GLOBAL', 'jvm_args').split())
    java_args.append('-Djava.library.path='+lbprefix + '/lib')
    java_args.extend(['-jar', lbprefix + '/share/java/lb-compiler.jar'])

    
    if args.command == 'file':
      java_args.append('compileFile')
      java_args.extend(['-stage', args.stage])
      java_args.extend(['-lifetime', args.lifetime])
      if args.out_format != None:
        java_args.extend(['-outputFormat', args.out_format])
      if args.serialize != None:
        if (args.out_format != 'proto'):
          raise lb_exception.ArgumentParserError('--serialize must be used with --out-format proto.')
        java_args.extend(['-serialize', args.serialize])
      if getattr(args, 'logic-file') != None:
        java_args.append(getattr(args, 'logic-file'))
      else:
        java_args.append('-stdin')
      

    if args.command == 'project':
      java_args.append('compileProject')
      if args.out_dir != None:
        java_args.extend(['-outDir', args.out_dir])
      if args.libpath != None:
        java_args.extend(['-libPath', args.libpath])
      if args.max_problems != None:
        java_args.extend(['-maxProblems', str(args.max_problems)])
      if args.clean:
        java_args.append('-clean')
      if args.progress:
        java_args.append('-progress')
      if args.explain:
        if not args.progress:
          java_args.append('-progress')
        java_args.append('-explain')
      java_args.append(getattr(args, 'project-file'))


    os.execvpe('java', java_args, subenv)
