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


"""
Errors raised by the lb command line interface.
"""

import traceback, os

class LBServerOff(Exception):
    """
        Throw when trying to connect to some server and it is OFF. By default this is the
        lb server, but it can be used for lb web server, compiler server, etc.

        This will cause the main script to exit with 1, to indicate failure.
    """
    def __init__(self, msg="lb server is OFF"):
        super(LBServerOff, self).__init__(msg)
        self.msg = msg
        self.stack = traceback.extract_stack()


class LBException(Exception):
    def __init__(self, msg):
        super(LBException, self).__init__(msg)
        self.msg = msg
        self.stack = traceback.extract_stack()

    def __repr__(self):
        return str(self)

    def __str__(self):
        if 'LB_DEBUG' in os.environ:
            return '%s\n%s' % (self.msg, ''.join(traceback.format_list(self.stack)))
        else:
            return self.msg

class LBCommandAPIException(LBException):
    """
        Error caused by problems in the implementation of commands.
    """
    pass

class LBCommandError(LBException):
    """ 
        Error during the execution of a command.
    """

    def __init__(self, msg=None, code=1):
        """
            @param msg a message to be displayed in stderr. If the message is
            None, it will not be displayed.
            @param code the integer value to be returned by the process in 
            sys.exit.
        """
        super(LBCommandError, self).__init__(msg)
        self.msg = msg
        self.code = code
        

class LBCommandArgsError(LBCommandError):
    """argument error"""
    def __init__(self, msg, code=2):
        # override this in subclasses
        super(LBCommandArgsError, self).__init__(msg, code)


class ArgumentParserError(LBException):
    """Custom ArgumentParserError Exception"""
    pass

class ExpectExceptionError(LBException):
    """used when expectException doesn't catch exception"""
    pass

class DeprecatedCommandError(LBException):
    """used for deprecated commands"""
    def __init__(self, command, extra=''):
        self.msg = "%s command has been deprecated. %s\n" % (command, extra)
        self.dep_command = command
        super(DeprecatedCommandError, self).__init__(self.msg)

class LBExit(Exception):
    """Explicit exit invocation"""
    def __init__(self, msg=None, code=0):
        super(Exception, self).__init__(msg)
        self.code = code

class LBReportedException(Exception):
    """Exceptions that have already been reported, and only need to be propagated."""
    def __init__(self, cause):
        super(Exception, self).__init__(u', caused by ' + repr(cause))
        self.cause = cause
