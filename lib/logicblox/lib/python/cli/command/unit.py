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

import lbunit.lb_unit

# do not install this command if in production environment
is_production = False

def add_commands(parser, subparsers):
    """

        Add this command to the main parser.
    """
    subparser = subparsers.add_parser('unit', help='lb unit')
    argparser(subparser)


def argparser(parser):
    parser.add_argument('--suite',
                        nargs='+',
                        help="list of test suites to run")
    parser.add_argument('--suite-dir',
                        dest='suiteDir',
                        nargs='+',
                        help="directory containing suites")
    parser.add_argument('--test',
                        nargs='+',
                        help="list of tests to run")
    parser.add_argument('--progress', '-p',
                        default=False,
                        action='store_true',
                        help="print each test name as it runs")
    parser.add_argument('--list', '-l',
                        default=False,
                        action='store_true',
                        help="display list of tests without running them")
    parser.add_argument('--time',
                        default=False,
                        action='store_true',
                        help="use measure engine for this workspace")
    parser.add_argument('--sequential', '-s',
                        default=False,
                        action='store_true',
                        help='run tests sequentially')
    parser.add_argument('--threads', '-t',
                        #nargs=1,
                        help='set number of threads, default to 1')
    parser.add_argument('--exclude-test',
                        dest='excludeTest',
                        nargs='+',
                        help="list of tests to exclude")
    parser.add_argument('--exclude', '-e',
                        nargs='+',
                        help="list of suites to exclude")
    parser.add_argument('--no-ignore',
                        dest='noIgnore',
                        default=False,
                        action='store_true',
                        help="do not ignore suites that have 'suite.ignore' files")
    parser.add_argument('--no-cleanup',
                        dest='noCleanup',
                        default=False,
                        action='store_true',
                        help="do not run teardown after each test")
    parser.add_argument('--default-fixtures',
                        dest='defaultFixtures',
                        default=False,
                        action='store_true',
                        help="run default test fixtures if no setup or teardown files exists")

    parser.set_defaults(func=lbunit.lb_unit.main)

    return parser

