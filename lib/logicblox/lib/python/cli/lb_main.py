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
import argparse, argcomplete
import errno
import importlib
import os
import sys

import lb_exception
import lbparser
import util

def run(command_line, lb_interactive_available=True):
    """
        Execute lb with this command line arguments (should not contain initial 'lb').

        @param command_line the full command line as a string.
        @param lb_interactive_available whether lb interactive sources are installed (usually they
            are not installed for lb web-client builds)
        @return the value returned by the function executed as a command for the command line.
    """

    # build the basic parser and parse the known arguments
    parser = build_parser(lb_interactive_available)
    args, extra = parser.parse_known_args(command_line)

    # see which type of function to execute, depending on the selected command
    if hasattr(args, 'func'):
        if extra:
            raise lb_exception.ArgumentParserError('unrecognized arguments: %s' % ' '.join(extra))
        return args.func(args)

    elif hasattr(args, 'extra_func'):
        return args.extra_func(args, extra, command_line)

    else:
        raise lb_exception.LBCommandAPIException('Command does not return proper function to be executed.')


def main(command_line, lb_interactive_available=True):
    """
        Execute this command line. Return 0 on success and some error code on failure.

        @param command_line the full command line as a string.
        @return 0 if the command line executed correctly, some error code on failure.
    """
    try:

        # run command and potentially use its return value
        ret = run(command_line, lb_interactive_available)
        if isinstance(ret, int) and not isinstance(ret, bool):
            return ret
        return 0

    except lb_exception.ArgumentParserError, ex:
        if ex.message.startswith("invalid choice") and len(command_line) == 1:
            print "'%s' is neither a recognized command nor a script file with a .lb suffix" % command_line[0]
        else:
            print ex.message
        # we only advice to use --help, without the used command, because it is difficult here to identify
        # which command was used, since we have very deep commands, and argparser does not help.
        print
        print "use '--help' for more help"
                
        return 2

    except lb_exception.LBServerOff, ex:
        print >> sys.stderr, ex
        return 1

    except lb_exception.LBCommandArgsError, ex:
        print >> sys.stderr, 'improper usage: %s' % str(ex)
        try:

           # we can assume the 0th element is the action b/c if not,
           # argparse would have blown up by now

            run([command_line[0], '-h'])
        except SystemExit:
            pass
        return 1

    except lb_exception.LBCommandError, ex:
        if ex.msg is not None:
            msg = ex.msg
            if 'error' in msg:
                print >> sys.stderr, msg
            else:
                print >> sys.stderr, 'error: %s' % msg

        return(ex.code)

    except KeyboardInterrupt:
        return 1

    except IOError as e:
        # Silently allow pipe errors that are thrown when the
        # sys.stdout is closed, for example due to piping the output
        # into less or head -1.
        if e.errno == errno.EPIPE:
            return 1
        else:
            raise


def build_parser(lb_interactive_available=True):
    """
        Create and return a command line parser. The parser is initialized
        with all commands that are found in the command directory.
    """

    # lookup commands
    commands = []
    command_dir = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'command')
    for dirpath, dirnames, filenames in os.walk(command_dir):
        for filename in filenames:
            if filename.endswith('.py') and not filename.startswith('.') and filename != '__init__.py':
                commands.append(filename[:-3])

    # create the main parser with our own help formatter
    if lb_interactive_available:
        parser = lbparser.LBArgumentParser(prog='lb', formatter_class=lbparser.LBHelpFormatter)
        subparsers = parser.add_subparsers(title='db commands')
    else:
        parser = argparse.ArgumentParser(prog='lb', formatter_class=lbparser.CLICommandHelpFormatter)
        subparsers = parser.add_subparsers(title='commands')

    # add global --version option if file exists
    with open(os.environ.get('LOGICBLOX_HOME') + "/libexec/logicblox/version") as file:
        version = file.read().rstrip()
    parser.add_argument('--version', '-v', action='version', help='print lb version', version=version)

    # ask commands to register themselves to the parser
    for command in commands:
        try:
            module = importlib.import_module('cli.command.' + command)

            if not util.is_production() or not hasattr(module, 'is_production') or module.is_production is not False:
                #print 'loading ' + str(module)
                module.add_commands(parser, subparsers)

        except ImportError, e:
            import traceback
            traceback.print_exc()
            print e
            raise lb_exception.LBCommandAPIException('Could not import module for command: ' + command)
        except AttributeError, e:
            import traceback
            traceback.print_exc()
            print e
            raise lb_exception.LBCommandAPIException('Command does not implement add_commands(parser, subparsers) function: ' + command)

    argcomplete.autocomplete(parser)
    lbparser.set_formatter(lbparser.list_subparsers(parser))
    return parser


