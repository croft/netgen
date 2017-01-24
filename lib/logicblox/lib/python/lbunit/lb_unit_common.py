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
from cli import lb_exception
import timeit

def run_file(file_name, interactive, test, comment=None):
    """run file_name using the interactive object and catch errors"""

    if file_name is None:
        return
    try:
        interactive.stdin = open(file_name)
        timer = timeit.timeit('%s' % interactive.cmdloop())
        test.testtimer += timer

    except lb_exception.LBCommandError, error:
        if 'Constraint failure' in str(error):
            test.state = State.FAILURE
            test.messages.append(Failure(error, file_name, comment))
        else:
            test.state = State.ERROR
            test.messages.append(Error(error, file_name, comment))

    except lb_exception.LBReportedException, ex:
        test.state = State.ERROR
        test.messages.append(Error(ex.cause, file_name, comment))

    except lb_exception.ExpectExceptionError, error:
        test.state = State.FAILURE
        test.messages.append(Failure(error, file_name, comment))
        
    except Exception, error:
        test.state = State.ERROR
        test.messages.append(Error(error, file_name, comment))


class Error(object):

    def __init__(self, error, test_name, comment=None):
        if hasattr(error, 'line_num'):
            self.line_num = error.line_num
        else:
            self.line_num = -1
        if hasattr(error, 'line'):
            self.line = error.line
        else:
            self.line = 'N/A'
        self.details = str(error)
        self.type = error.__class__.__name__
        self.test_name = test_name
        self.comment = comment


class Failure(Error):

    def __init__(self, error, test_name, comment=None):
        Error.__init__(self, error=error, test_name=test_name, comment=comment)


class State:

    SUCCESS = '.'
    FAILURE = 'F'
    ERROR = 'E'


