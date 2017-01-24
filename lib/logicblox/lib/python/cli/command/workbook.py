"""
Copyright 2014 LogicBlox, Inc.

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

# default error message (may change)
ERROR_MSG = 'WARNING: Workbook services are not installed. Please install and set environment variable LB_WORKBOOK_SERVICE_HOME.'

webserver_home = os.environ.get('LB_WEBSERVER_HOME')
workbooks_home = os.environ.get('LB_WORKBOOK_SERVICE_HOME')
WORKBOOKS_IS_INSTALLED = False

if not webserver_home:
    ERROR_MSG = ("warning: lb-web-server installation is not known."
                 " Please load etc/profile.d/logicblox.sh or manually set LB_WEBSERVER_HOME.")
elif not workbooks_home:
    ERROR_MSG = ("warning: lb-workbook-service installation is not known."
                 " Please load etc/profile.d/logicblox.sh or manually set LB_WORKBOOK_SERVICE_HOME.")
elif not os.path.isdir(workbooks_home):
    ERROR_MSG = "warning: LB_WORKBOOK_SERVICE_HOME is set to '%s', but this directory does not exists" % os.environ.get('LB_WORKBOOK_SERVICE_HOME')
else:
    # This confirms that witness files exist
    lb_workbooks_files = [
        'lib/python/lb_web_workbooks/workbooks_pb2.py',
        'lib/java/lb-web-workbooks.jar'
    ]

    # Note: do *not* add inference of candidates.
    verified_home = cli.util.find_home([], lb_workbooks_files, ['LB_WORKBOOK_SERVICE_HOME'])

    if not verified_home:
        ERROR_MSG = ("warning: LB_WORKBOOK_SERVICE_HOME is set to '%s', but this directory "
                     "does not appear to contain an lb-workbook-service distribution."  % os.environ.get('LB_WORKBOOK_SERVICE_HOME'))
    else:
        os.environ['LB_WORKBOOK_SERVICE_HOME'] = workbooks_home

        sys.path.insert(0, '%s/lib/python' % workbooks_home)
        sys.path.insert(0, '%s/lib/python' % webserver_home)
        try:
            # Need to import like this so that globals() will list all functions in the webserver module.
            # This may fail if the webserver_home does not point to a proper distribution (or to an older one)
            from lb_web_workbooks.workbook import *
            WORKBOOKS_IS_INSTALLED = True

        except Exception,e:
            ERROR_MSG = ("warning: LB_WORKBOOK_SERVICE_HOME is set to '%s', but this does not appear to be an "
                         "lb-workbook-service distribution.\n Exception: '%s'" % (os.environ.get('LB_WORKBOOK_SERVICE_HOME'),e))
            pass

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """

    # The main sub-command parser
    main_subparser = subparsers.add_parser(
        'workbook', help='workbook services' if WORKBOOKS_IS_INSTALLED else '',
        description=ERROR_MSG if not WORKBOOKS_IS_INSTALLED else None)

    if WORKBOOKS_IS_INSTALLED:
        add_workbook_commands(main_subparser)
    else:
        main_subparser.set_defaults(extra_func=no_workbooks)

def no_workbooks(args, extra, command_line):
    raise cli.lb_exception.LBServerOff(ERROR_MSG)

    

