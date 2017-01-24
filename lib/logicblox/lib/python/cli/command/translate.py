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

# do not install this command if in production environment
is_production = False

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('translate', help='dummy translate')
    subparser.set_defaults(func=execute_unit) 


def execute_unit(args):
    """
        Execute this command.
    """
    print 'running translate!!!'
