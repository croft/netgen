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

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('disassemble', help='disassemble LogicBlox project summary (lbp) and bytecode (lbb) files')
    subparser.set_defaults(func=execute_disassemble)

    subparser.add_argument('files',
                           nargs='+',
                           help="lbp and lbb files to disassemble")

    subparser.add_argument('--out-format',
                           choices=['lb0', 'protobuf'],
                           help="selects output format for lbb inputs files.  Either pretty printed LB0 or the text serialization of the Google protocol representation.  Defaults to lb0.  Protocol buffer output must be used with lbp files")

    subparser.add_argument('--header',
                           default=False,
                           action='store_true',
                           help="attempts to parse out the header of an lbb or lbp file. Useful for debugging invalid or corrupt files")
    subparser

def execute_disassemble(args):
    """
        Execute this command.
    """

    config = util.load_default_config('lb-compiler')
    subenv = os.environ.copy()
    lbprefix = subenv.get('LOGICBLOX_HOME')

    java_args = ['java']
    if not util.is_production():
      java_args.append('-ea')
    if config.has_option('GLOBAL', 'jvm_args'):
        java_args.extend(config.get('GLOBAL', 'jvm_args').split())
    java_args.append('-Djava.library.path='+lbprefix + '/lib')
    java_args.extend(['-cp', lbprefix + '/share/java/lb-compiler.jar'])
    java_args.append('com.logicblox.compiler.disassembler.Disassembler')

    if args.header:
      java_args.append('--header')
    if args.out_format == 'lb0':
      java_args.append('--lb0')
    if args.out_format == 'protobuf':
      java_args.append('--protobuf')

    java_args.extend(args.files)

    os.execvpe('java', java_args, subenv)



