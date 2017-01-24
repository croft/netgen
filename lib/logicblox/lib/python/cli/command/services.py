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
import subprocess
import os
import sys

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """
    services_parser = subparsers.add_parser('services', help='manage lb services')

    services_subparsers = services_parser.add_subparsers(title='Commands')
    
    if not cli.util.is_production(): 
        cmd_parser = services_subparsers.add_parser('start', help='start a service')
        cmd_parser.set_defaults(func=start)

        cmd_parser = services_subparsers.add_parser('stop', help='stop a running service')
        cmd_parser.set_defaults(func=stop)

        cmd_parser = services_subparsers.add_parser('restart', help='stop and start a service')
        cmd_parser.set_defaults(func=restart)

        cmd_parser = services_subparsers.add_parser('print', help='list processes of running services')
        cmd_parser.set_defaults(func=print_services)

    cmd_parser = services_subparsers.add_parser('processes', help='list processes related to running services by heuristic')
    cmd_parser.set_defaults(func=print_processes)

    cmd_parser = services_subparsers.add_parser('status', help='print the status of services')
    cmd_parser.set_defaults(func=status)


def handle(args):
    print args

def call_lb_services(cmd):
    p = subprocess.Popen([os.path.expandvars('$LOGICBLOX_HOME/libexec/logicblox/lb-services')] + cmd, stdout=sys.stdout, stderr=sys.stderr)
    p.communicate()
    if p.returncode != 0:
      sys.exit(p.returncode)

def print_services(args):
    call_lb_services(['print'])

def print_processes(args):
    call_lb_services(['processes'])

def status(args):
    call_lb_services(['status'])

def start(args):
    call_lb_services(['start'])

def stop(args):
    call_lb_services(['stop'])

def restart(args):
    call_lb_services(['restart'])

