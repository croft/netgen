"""
Copyright 2015 LogicBlox, Inc.

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
ERROR_MSG = 'WARNING: Workflow services are not installed. Please install and set environment variable LB_WORKFLOW_HOME.'

workflow_home = os.environ.get('LB_WORKFLOW_HOME')
WORKFLOW_IS_INSTALLED = False

if not workflow_home:
    ERROR_MSG = ("warning: lb workflow installation is not known."
                 " Please load etc/profile.d/logicblox.sh or manually set LB_WORKFLOW_HOME.")
elif not os.path.isdir(workflow_home):
    ERROR_MSG = "warning: LB_WORKFLOW_HOME is set to '%s', but this directory does not exists" % os.environ.get('LB_WORKFLOW_HOME')
else:
    # This confirms that witness files exist
    lb_workflow_files = [
        'lib/python/lb_workflow/testcase.py',
        'lib/java/lb-workflow.jar'
    ]

    # Note: do *not* add inference of candidates.
    verified_home = cli.util.find_home([], lb_workflow_files, ['LB_WORKFLOW_HOME'])

    if not verified_home:
        ERROR_MSG = ("warning: LB_WORKFLOW_HOME is set to '%s', but this directory "
                     "does not appear to contain an lb workflow distribution."  % os.environ.get('LB_WORKFLOW_HOME'))
    else:
        os.environ['LB_WORKFLOW_HOME'] = workflow_home

        sys.path.insert(0, '%s/lib/python' % workflow_home)
        try:
            # Need to import like this so that globals() will list all functions in the workflow module.
            # This may fail if the webserver_home does not point to a proper distribution (or to an older one)
            from lb_workflow.workflow import *
            WORKFLOW_IS_INSTALLED = True

        except Exception,e:
            ERROR_MSG = ("warning: LB_WORKFLOW_HOME is set to '%s', but this does not appear to be an "
                         "lb workflow distribution.\n Exception: '%s'" % (os.environ.get('LB_WORKFLOW_HOME'),e))
            pass

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """

    # The main sub-command parser
    main_subparser = subparsers.add_parser(
        'workflow', help='workflow' if WORKFLOW_IS_INSTALLED else '',
        description=ERROR_MSG if not WORKFLOW_IS_INSTALLED else None)

    if WORKFLOW_IS_INSTALLED:
        add_workflow_commands(main_subparser)
    else:
        main_subparser.set_defaults(extra_func=no_workflows)

def no_workflows(args, extra, command_line):
    raise cli.lb_exception.LBServerOff(ERROR_MSG)

    

