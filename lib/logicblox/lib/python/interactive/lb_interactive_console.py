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

import sys
import os
import blox.connect.io
import cmd
import shlex
import logging
from subprocess import call
import string
import re
import time
import socket
import glob
import traceback

from dbcommands.lb_all_commands import _get_workspaces, _get_predicates, _get_blocks, _get_options
import dbcommands.lb_argparser
from cli import lb_exception
import cli.lbparser

# the default prompt when using lb interactive
PROMPT='lb'

# debug mode can be set with an environment variable
LB_DEBUG='LB_DEBUG' in os.environ

LOGGER = logging.getLogger('lb_interactive_console')


# This class is used for tab completion and history
class LbInteractive(cmd.Cmd):
    def __init__(self, stop_on_error=True, use_rawinput=True, stdout=sys.__stdout__, stdin=None,
                 cmdqueue=None, dev=False, current_directory=os.getcwd(), set_dict=None):
        import readline
        cmd.Cmd.__init__(self, stdout=stdout, stdin=stdin)
        self.history_log_path = os.environ['HOME'] + '/.lb_history.txt';
        conn = blox.connect.io.Connection(False)
        try:
            conn.open()
        except socket.error:
            print "Server is OFF. Start using lb services start."
            sys.exit(1)

        self.stop_on_error = stop_on_error
        self.current_directory = current_directory
        self.use_rawinput = use_rawinput
        # dev specifies developer features, such as prevent error catching
        self.dev = dev  
        # sets the command queue if it is included
        self.cmdqueue = cmdqueue        

        if set_dict is None:
            self.set_dict = {}
        else:
            self.set_dict = set_dict
        
        try:
            history = open(self.history_log_path, 'r+').read().split('\n----------\n')[:-1];
            for line in history:
                    readline.add_history(line)
        except IOError:
            open(self.history_log_path, 'w+')

        self.parser = dbcommands.lb_argparser.BuildLBInteractiveParser(self.current_directory).make()
        self.parser.formatter_class = cli.lbparser.LBHelpFormatter
        cli.lbparser.set_formatter(cli.lbparser.list_subparsers(self.parser))
        self.all_commands = self.parser._get_positional_actions()[0].choices.keys()

        # multi-line and tab completion functionality
        self.single_quotes = 0              # number of single quotes
        self.double_quotes = 0              # number of double quotes
        self.doc_start = False
        self.current_command = None         # stores current command (used for multiline)
        self.complete_command = None        # stores current command (used for tab completion)
        self.in_logic = False
        self.in_transaction = False

        self.identchars = string.ascii_letters + string.digits + '_' + ':'
        self.default_prompt = '%s> ' % PROMPT
        self.prompt = self.default_prompt
        self.multiline_prompt = '>'

        self.current_workspace = ''
        self.list_workspaces = _get_workspaces(self)
        self.loglevel = None
        self.timer = time.time()

        self.line_count = 0     # stores number of lines executed in current session

        self.transaction = LbInteractiveTransaction(
            stop_on_error=self.stop_on_error,
            cmdqueue=self.cmdqueue,
            use_rawinput=self.use_rawinput,
            stdout=self.stdout,
            stdin=self.stdin,
            dev=self.dev,
            current_directory=self.current_directory,
            set_dict=self.set_dict,
            )

    def __deepcopy__(self, memo):
        """used in lb_unit_concurrent to copy the interactive object"""
        new_interactive =  LbInteractive(
            use_rawinput=self.use_rawinput, 
            stdout=self.stdout, 
            stdin=self.stdin, 
            dev = self.dev,
            cmdqueue=self.cmdqueue, 
            current_directory=self.current_directory, 
            set_dict=self.set_dict.copy())
        new_interactive.current_workspace = self.current_workspace
        new_interactive.loglevel = self.loglevel
        return new_interactive

    def default(self,line,split=True):
        """
        override default from cmd module
        all commands (except shell commands and exit) go through default
        """
        if split:
            line = self.split_arguments(line)
        args = self.parser.parse_args(line)

        return args.func(args, self)

    def split_arguments(self, line):
        """
        takes a string and returns a list of arguments
        takes care of environment vairables and <doc> tags
        """

        # if find <doc></doc> tags, split text in between as one
        start = line.find('<doc>')
        end = line.rfind('</doc>')
        if start != -1 and end != -1:
            beginning = line[:start]
            group = line[start + len('<doc>'):end]
            ending = line[end + len('</doc>'):]
            commands = shlex.split(beginning)
            commands.append(group)
            commands.extend(shlex.split(ending))
        else:
            commands = shlex.split(line)

        # strip all whitespace
        return [command.strip() for command in commands]

    def onecmd_wrapper(self,line):
        """
        calls onecmd which then calls default or do_<command>
        catches all exceptions so REPL doesn't exit out
        """
        try:
            return self.onecmd(line)
        except SystemExit: # occurs after -h or when interrupted
                           # or timing out
            return True
        except lb_exception.LBExit, ex:
            raise ex
        except lb_exception.LBCommandArgsError, ex:
            ex.line_num = self.line_count
            ex.line = line
            if LB_DEBUG or self.dev:
                traceback.print_exc(ex)

            print "Improper usage: %s" % str(ex)
            # we can assume the 0th element is the action
            self.onecmd_wrapper(line.split()[0] + " -h")
            raise lb_exception.LBReportedException(ex)

        except lb_exception.LBCommandError, ex:
            ex.line_num = self.line_count
            ex.line = line
            if LB_DEBUG or self.dev:
                traceback.print_exc(ex)

            if ex.msg is not None:
                msg = ex.msg
                if 'error' in msg:
                    sys.stderr.write('%s\n' % msg)
                else:
                    sys.stderr.write('error: %s\n' % msg)

            raise lb_exception.LBReportedException(ex)

        except lb_exception.LBReportedException, ex:
            if LB_DEBUG or self.dev:
                traceback.print_exc(ex)
            raise ex

        except Exception as ex:
            ex.line_num = self.line_count
            ex.line = line
            if LB_DEBUG or self.dev:
                traceback.print_exc(ex)

            sys.stderr.write("%s: %s\n" % (ex.__class__.__name__, str(ex)))
            raise lb_exception.LBReportedException(ex)
                
    def precmd(self, line):
        # replace environment variables
        return self.replace_environ(line).strip()

    def start_command(self, line):    
        """catches errors from onecmd_wrapper, used for expectException"""          
        line = self.precmd(line)
        expect_exception = 'bloxunit:expectException' in self.set_dict
        stop = None

        def remove_exception_var():
            if 'bloxunit:expectException' in self.set_dict:
                self.set_dict.pop('bloxunit:expectException')

        try:
            stop = self.onecmd_wrapper(line)

        except (lb_exception.DeprecatedCommandError, lb_exception.ArgumentParserError) as ex:
            # if it's a deprecated error, we don't care if exception was expected
            remove_exception_var()
            self.in_transaction = False
            raise ex

        except Exception as ex:
            if line == 'transaction' and not expect_exception:
                expect_exception = 'bloxunit:expectException' in self.set_dict

            if expect_exception:
                remove_exception_var()
            else:
                self.in_transaction = False
                raise ex
        else:
            if line == 'transaction' and not expect_exception:
                expect_exception = 'bloxunit:expectException' in self.set_dict 
            if expect_exception and self.dev:
                remove_exception_var()
                e = lb_exception.ExpectExceptionError("Set Expect Exception Error: No Exceptions Raised.")
                e.line_num = self.line_count
                e.line = line
                raise e

        return stop

    # called after each file runs in lbunit (ie. after setup, testfile)
    def clear_variables(self):
        self.line_count=0
        self.cmdqueue = []

    def set_current_directory(self, curr_dir):
        self.current_directory = curr_dir
        self.parser.current_directory[0] = curr_dir
        
    def update_workspaces(self):
        self.list_workspaces = _get_workspaces(self)

    def set_curr_workspace(self,ws):
        self.current_workspace = ws
        if ws:
            self.prompt = '%s %s> ' % (PROMPT, ws) 
        else:
            self.prompt = self.default_prompt

    def replace_environ(self, text):
        """ replace environment variables such as ${LOGICBLOX_HOME}"""
        env_var_matcher = re.compile(r'\$\{\w+?\}')
        for match in env_var_matcher.finditer(text):
            env_match = match.group()
            var_strip = env_match[2:-1]
            shell_env = os.environ.get(var_strip)

            # first match with set dictionary
            if var_strip in self.set_dict:
                text = text.replace(env_match, self.set_dict[var_strip])
            # if there is no environment variable
            elif shell_env != None:
                text = text.replace(env_match, shell_env)
        return text

    def do_echo(self, arg):
        print arg

    """
    Deprecated commands that are still supported for backward compatibility
    """
   
    def deprecated_msg(self, deprecated, new):
        """warning for using a deprecated command"""
        print "\n*************************************"
        print "'%s' command has been deprecated." % deprecated
        print "Please use '%s' instead." % new
        print "*************************************\n"

    def do_shell(self, arg):
        # don't allow REPL within REPL
        if arg != 'lb':
            call(arg, stdout=sys.stdout, stderr=sys.stderr, shell=False)
            
    def do_expectError(self, arg):
        self.set_dict["bloxunit:expectException"] = "Exception"
        self.start_command(arg)

    # override help
    def do_help(self, arg):
        if arg:
            command = arg.split() + ['-h']
            self.default(command, split=False)
        else:
            self.default('-h')

    def do_startTimer(self, line):
        self.deprecated_msg('startTimer', 'starttimer')
        command = ['starttimer'] + self.split_arguments(line)
        self.default(command, split=False)

    def do_elapsedTime(self, line):
        self.deprecated_msg('elapsedTime', 'elapsedtime')
        command = ['elapsedtime'] + self.split_arguments(line)
        self.default(command, split=False)

    def do_installProject(self, line):
        self.deprecated_msg('installProject', 'addproject')
        command = ['addproject'] + self.split_arguments(line)
        try:
            if '-D' in command:
                self.relocate_args(command, '-D', 1)
            elif '--dir' in command:
                self.relocate_args(command, '--dir', 1)

            self.default(command, split=False)
        except IndexError:
            raise Exception("Error in installProject: required parameter is missing in 'dir'\n")

    def do_addBlock(self, line):
        self.deprecated_msg('addBlock', 'addblock')
        command = ['addblock'] + self.split_arguments(line)

        if '--lifetime transaction' in line:
            raise lb_exception.DeprecatedCommandError('--lifetime transaction in addBlock')
        if '--lifetime session' in line:
            raise lb_exception.DeprecatedCommandError('--lifetime session in addBlock')
        self.replace_deprecated_tags(command, ['-B'], ['--name'])
        self.replace_deprecated_tags(command, ['--blockName'], ['--name'])
        self.replace_deprecated_tags(command, ['-I'], ['--inactive'])
        self.replace_deprecated_tags(command, ['--active=false'], ['--inactive'])
        self.replace_deprecated_tags(command, ['--active', 'false'], ['--inactive'])
        self.replace_deprecated_tags(command, ['-A', 'false'], ['--inactive'])
        self.replace_deprecated_tags(command, ['--active', 'true'], [])
        self.replace_deprecated_tags(command, ['--active=true'], [])
        self.replace_deprecated_tags(command, ['-A', 'true'], [])
        self.replace_deprecated_tags(command, ['--lifetime', 'database'], [])
        self.replace_deprecated_tags(command, ['-M'], ['--measure'])

        self.default(command, split=False)

    def do_installLibrary(self, line):
        self.deprecated_msg('installLibrary', 'addlib')
        command = ['addlib'] + self.split_arguments(line)
        self.default(command, split=False)

    def do_exec(self, line):
        command = ['exec'] + self.split_arguments(line)

        #if '--input' in command:
        #    raise lb_exception.DeprecatedCommandError("--input option in exec")

        # change exec to execblock
        if '-S' in command:
            self.relocate_args(command, '-S', 1)
            self.replace_deprecated_tags(command, ['exec'], ['execblock'])
        elif '--storedBlock' in command:
            self.relocate_args(command, '--storedBlock', 1)
            self.replace_deprecated_tags(command, ['exec'], ['execblock'])
        self.replace_deprecated_tags(command, ['-F'], ['-f'])
        self.replace_deprecated_tags(command, ['--blockName'], ['--blockname'])
        self.default(command, split=False)

    def do_create(self, line):
        command = ['create'] + self.split_arguments(line)

        if '--copy' in command:
            raise lb_exception.DeprecatedCommandError("--copy option in create")
        if '--blocks' in command:
            raise lb_exception.DeprecatedCommandError("--blocks option in create")

        self.replace_deprecated_tags(command, ['-U'], ['--unique'])
        self.default(command, split=False)

    def do_close(self, line):
        command = ['close'] + self.split_arguments(line)
        self.replace_deprecated_tags(command, ['-D'], ['--destroy'])
        self.default(command, split=False)

    def do_logLevel(self, line):
        self.deprecated_msg('logLevel', 'loglevel')
        command = ['loglevel'] + self.split_arguments(line)
        self.default(command, split=False)

    def do_removeBlock(self, line):
        self.deprecated_msg('removeBlock', 'removeblock')
        command = ['removeblock'] + self.split_arguments(line)
        try:
            if '-B' in command:
                self.relocate_args(command, '-B', 1)
            elif '--blockName' in command:
                self.relocate_args(command, '--blockName', 1)

            self.default(command, split=False)
        except IndexError:
            raise Exception('Error in removeBlock: required parameter is missing\n')

    def do_replaceBlock(self, line):
        self.deprecated_msg('replaceBlock', 'replaceblock')
        command = ['replaceblock'] + self.split_arguments(line)
        try:
            if '--blockName' in command:
                self.relocate_args(command, '--blockName', 1)
            elif '-B' in command:
                self.relocate_args(command, '-B', 1)
        except IndexError:
            raise Exception("Error in replaceBlock: required parameter is missing in 'name'\n")

        self.replace_deprecated_tags(command, ['-F'], ['-f'])

        if not ('--file' in command or '-f' in command) and len(command) > 2:
            command.insert(len(command) - 1, '--logic')

        self.default(command, split=False)

    def do_predInfo(self, line):
        self.deprecated_msg('predInfo', 'predinfo')
        command = ['predinfo'] + self.split_arguments(line)
        self.default(command, split=False)

    def do_buildProject(self, line):
        self.deprecated_msg('buildProject', 'addproject')
        command = ['addproject'] + self.split_arguments(line)
        try:
            if '-D' in command:
                self.relocate_args(command, '-D', 1)
            elif '--dir' in command:
                self.relocate_args(command, '--dir', 1)

            self.default(command, split=False)
        except IndexError:
            raise Exception("Error in buildProject: required parameter is missing in 'dir'\n")

    def do_protoImport(self, line):
        self.deprecated_msg('protoImport', 'import-protobuf')
        command = ['import-protobuf'] + self.split_arguments(line)
        
        try:
            if '--proto' in command:
                self.relocate_args(command, '--proto', 1)
            if '--msgType' in command:
                self.relocate_args(command, '--msgType', 2)
            if '--file' in command:
                self.relocate_args(command, '--file', 3)

            self.replace_deprecated_tags(command, ['--block', ''], [''])
            self.default(command, split=False)
        except IndexError:
            raise Exception('Error in protoImport: required parameter is missing\n')

    def do_protoExport(self, line):
        self.deprecated_msg('protoExport', 'export-protobuf')
        command = ['export-protobuf'] + self.split_arguments(line)
        
        try:
            if '--proto' in command:
                self.relocate_args(command, '--proto', 1)
            if '--msgType' in command:
                self.relocate_args(command, '--msgType', 2)
            if '--file' in command:
                self.relocate_args(command, '--file', 3)

            self.replace_deprecated_tags(command, ['--block', ''], [''])
            self.default(command, split=False)
        except IndexError:
            raise Exception('Error in protoExport: required parameter is missing\n')

    def do_protoAddSpec(self, line):
        self.deprecated_msg('protoAddSpec', 'import-protobuf-schema')
        command = ['import-protobuf-schema'] + self.split_arguments(line)
        try:
            if '--name' in command:
                self.relocate_args(command, '--name', 1)
            if '--file' in command:
                self.relocate_args(command, '--file', 2)

            self.default(command, split=False)
        except IndexError:
            raise Exception('Error in protoAddSpec: required parameter is missing\n')

    def do_xmlAddSpec(self, line):
        self.deprecated_msg('xmlAddSpec', 'import-xml-schema')
        command = ['import-xml-schema'] + self.split_arguments(line)
        try:
            if '--name' in command:
                self.relocate_args(command, '--name', 1)
            if '--file' in command:
                self.relocate_args(command, '--file', 2)

            self.default(command, split=False)
        except IndexError:
            raise Exception('Error in xmlAddSpec: required parameter is missing\n')

    def do_xmlImport(self, line):
        self.deprecated_msg('xmlImport', 'import-xml')
        command = ['import-xml'] + self.split_arguments(line)
        try:
            if '--file' in command:
                self.relocate_args(command, '--file', 1)

            self.default(command, split=False)
        except IndexError:
            raise Exception("Error in xmlImport: required parameter is missing in 'file'\n")

    def relocate_args(self,command,tag,i,):
        """
        helper function for deprecated commands for backwards compatibility
        relocate the argument following 'tag' in 'cmd' to 'i'.
        """
        arg = command[command.index(tag) + 1]
        command.remove(arg)
        command.remove(tag)
        command.insert(i, arg)

        return command

    def replace_deprecated_tags(self,command,tags,replacement):
        """
        helper function for deprecated commands for backwards compatibility
        replace optional tags with ones accepted by lb
        """
        # a single option can have more than one tags
        # however, the command list splits the option apart due to the space in between tags
        # if the option has one tag, then there is not splitting, 
        # so the option can be found in the command list  
        if (len(tags) == 1):
            cmd_string = command
            tags_string = tags[0]
        # if the option has more than one tag, the command list and the tags list must be joined
        # in order to find the option in the command
        else:
            cmd_string = ' '.join([c for c in command if c != ''])
            tags_string = ' '.join(tags)

        if tags_string in cmd_string:
            start_index = command.index(tags[0])

            # remove tags

            for i in range(len(tags)):
                command.pop(start_index)

            # insert replacement

            for i in range(len(replacement)):
                command.insert(start_index + i, replacement[i])
        return command

    """
    Deprecated Commands that are no longer supported
    """

    def do_option(self, arg):
        raise lb_exception.DeprecatedCommandError('option')
    def do_watch(self, arg):
        raise lb_exception.DeprecatedCommandError('watch')
    def do_comparePredicates(self, arg):
        raise lb_exception.DeprecatedCommandError('comparePredicates')
    def do_execRetry(self, arg):
        raise lb_exception.DeprecatedCommandError('execRetry')
    def do_loadLibrary(self, arg):
        raise lb_exception.DeprecatedCommandError('loadLibrary', 'Use -lib option when creating a workspace.')
# end of deprecated commands

# argument completion

    def completedefault(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)

    def complete_open(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.workspaces_completion(text)

    def complete_delete(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.workspaces_completion(text)

    def complete_export(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.workspaces_completion(text)

    def complete_exportprotobuf(self, text, line, begidx, endidx, arg_len):
        if arg_len == 3:
            return glob.glob(text+'*')

    def complete_importprotobuf(self, text, line, begidx, endidx, arg_len):
        if arg_len == 3:
            return glob.glob(text+'*')

    def complete_protoaddspec(self, text, line, begidx, endidx, arg_len):
        if arg_len == 2:
            return glob.glob(text+'*')

    def complete_xmladdspec(self, text, line, begidx, endidx, arg_len):
        if arg_len == 3:
            return glob.glob(text+'*')

    def complete_version(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.workspaces_completion(text)

    def complete_predinfo(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.predicates_completion(text)

    def complete_print(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.predicates_completion(text)

    def complete_addblock(self, text, line, *ignored):
        # complete predicates even if there is a '+' or '-' in front
        pred_chars = ['+', '-', '!', '(', "'"]
        args = line.split(' ')
        if not self.in_logic and text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        # if current text right after -f or --file tag
        elif len(args) >= 2 and (args[-2] == '-f' or args[-2] == '--file'):
            return glob.glob(text+'*')
        elif '@' in text:
            split_text = text.split('@', 1)
            pred_list = self.stages_completion(split_text[1])
            pred_list = [split_text[0] + '@' + word for word in pred_list]
            return pred_list
        # if starts with any of the pred_chars
        elif len(text) != 0 and any(text.startswith(char) for char in pred_chars):
            first_char = text[0]
            text = text[1:]
            pred_list = self.predicates_completion(text)
            pred_list = [first_char + word for word in pred_list]
            return pred_list
        else:
            return self.predicates_completion(text)

    def complete_compileblock(self, text, line, begdx, endidx, num_arguments):
        pred_chars = ['+', '-', '!', '(', "'"]
        args = line.split(' ')

        if not self.in_logic and text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        elif len(args) >= 2 and (args[-2] == '-f' or args[-2] == '--file'):
            return glob.glob(text+'*')
        elif '@' in text:
            split_text = text.split('@', 1)
            pred_list = self.stages_completion(split_text[1])
            pred_list = [split_text[0] + '@' + word for word in pred_list]
            return pred_list
        elif len(text) != 0 and any(text.startswith(char) for char in
                                    pred_chars):
            first_char = text[0]
            text = text[1:]
            pred_list = self.predicates_completion(text)
            pred_list = [first_char + word for word in pred_list]
            return pred_list
        else:
            return self.predicates_completion(text)

    def complete_exec(self, text, line, begdx, endidx, num_arguments):
        pred_chars = ['+', '-', '!', '(', "'"]
        args = line.split(' ')
        if not self.in_logic and text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        elif len(args) >= 2 and (args[-2] == '-f' or args[-2] == '--file'):
            return glob.glob(text+'*')
        elif '@' in text:
            split_text = text.split('@', 1)
            pred_list = self.stages_completion(split_text[1])
            pred_list = [split_text[0] + '@' + word for word in pred_list]
            return pred_list
        elif len(text) != 0 and any(text.startswith(char) for char in pred_chars):
        # elif len(text) != 0 and (text[0] == '+' or text[0] == '-'):

            first_char = text[0]
            text = text[1:]
            pred_list = self.predicates_completion(text)
            pred_list = [first_char + word for word in pred_list]
            return pred_list

        else:
            return self.predicates_completion(text)

    def complete_removeblock(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.blocks_completion(text)

    def complete_replaceblock(self, text, *ignored):
        args = line.split(' ')

        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        elif len(args) >= 2 and (args[-2] == '-f' or args[-2] == '--file'):
            return glob.glob(text+'*')
        else:
            return self.blocks_completion(text)

    def complete_execblock(self, text, *ignored):
        if text.startswith('-'):
            return self.options_completion(self.complete_command, text)
        else:
            return self.blocks_completion(text)

    def complete_source(self, text, line, *ignored):
        return glob.glob(text+'*')

    def complete_save(self, text, line, begidx, endidx, arg_len):
        return glob.glob(text+'*')

    def complete_query(self, text, line, *ignored):
        args = line.split(' ')
        if len(args) >= 2 and (args[-2] == '-f' or args[-2] == '--file'):
            return glob.glob(text+'*')
        else:
            return self.predicates_completion(text)

    # use this to complete a list of workspaces
    def workspaces_completion(self, text):
        completions = self.list_workspaces
        if not text:
            return completions
        else:
            return [f for f in completions if f.startswith(text)]

    # use this to complete predicates
    def predicates_completion(self, text):
        if self.current_workspace:
            completions = _get_predicates(self)
            if not text:
                return completions
            else:
                return [f for f in completions if f.startswith(text)]
        else:
            return

    # use this to complete blocks
    def blocks_completion(self, text):
        if self.current_workspace:
            completions = _get_blocks(self)
            if not text:
                return completions
            else:
                return [f for f in completions if f.startswith(text)]
        else:
            return

    def options_completion(self, name, text):
        completions = _get_options(name, self)
        if not text:
            return completions
        else:
            return [f for f in completions if f.startswith(text)]

    # used for @ tags
    def stages_completion(self, text):
        completions = ['prev', 'previous', 'init', 'initial', 'final']
        if not text:
            return completions
        else:
            return [f for f in completions if f.startswith(text)]

    # override complete: addded arg_len and current_command
    def complete(self, text, state):
        """Return the next possible completion for 'text'.
        If a command has not been entered, then complete against command list.
        Otherwise try to call complete_<command> to get list of completions.
        """
        if state == 0:
            import readline
            origline = readline.get_line_buffer()
            line = origline.lstrip()
            stripped = len(origline) - len(line)
            begidx = readline.get_begidx() - stripped
            endidx = readline.get_endidx() - stripped
            # arg_len is useful if a command has >1 argument,
            # say, workspace and predicate. Then it is useful to know
            # which argumentstderr.write you are on to know which completion to use.
            # however, so far there are no commands that has two different completion
            arg_len = 0

            if (self.single_quotes + line.count("'")) % 2 == 1 \
                or (self.double_quotes + line.count('"')) % 2 == 1 \
                or self.doc_start:
                self.in_logic = True
            else:
                self.in_logic = False

            # this means this is on a multi-line
            if self.current_command:
                command = self.current_command
                try:
                    compfunc = getattr(self, 'complete_' + command)
                except AttributeError:
                    compfunc = self.completedefault
            elif begidx > 0:

                (command, args, junk) = self.parseline(line)
                arg_len = len(args.split())
                if command == '':
                    compfunc = self.completedefault
                else:
                    try:
                        compfunc = getattr(self, 'complete_' + command)
                    except AttributeError:
                        compfunc = self.completedefault
                self.complete_command = command
            else:
                compfunc = self.completenames

            # if current text is empty, another argument is added
            if not text.strip():
                arg_len += 1
            self.completion_matches = compfunc(text, line, begidx,
                    endidx, arg_len)
        try:
            return self.completion_matches[state]
        except IndexError:
            return None

    # override completenames: complete from currentCommands list
    def completenames(self, text, *ignored):
        return [a[0:] for a in self.all_commands if a.startswith(text)]

    # overwrite cmdloop: '
    # - change delimeter to space
    # - support multi line with quotes
    # - support multi line with <doc> logic </doc>
    # - call startcommand instead of onecmd
    def cmdloop(self):
        """Repeatedly issue a prompt, accept input, parse an initial prefix
        off the received input, and dispatch to action methods, passing them
        the remainder of the line as argument.
        Will first take command from cmdqueue. If it is empty, will take from stdin.
        """
        import readline
        if self.use_rawinput and self.completekey:
            try:
                # only delimiter is space
                readline.set_completer_delims(" ") 
                self.old_completer = readline.get_completer()
                readline.set_completer(self.complete)
                readline.parse_and_bind(self.completekey+": complete")
            except ImportError:
                pass
        try:
            stop = None
            really_stop = False

            self.single_quotes = 0  # number of single quotes
            self.double_quotes = 0  # number of double quotes

            multi_comment = False
            multiline_start = False  # True if multiline started

            line_so_far = ''    # if multi lines, stores the appended lines
            prevline = ''       # used for duplicates
            multi_count = 0     # stores how many lines there have been


            # start loop
            while not (really_stop or stop and self.stop_on_error):
                self.line_count += 1
                used_rawinput = False

                # get input
                if self.cmdqueue:
                    line = self.cmdqueue.pop(0)
                else:
                    if self.use_rawinput:
                        used_rawinput = True
                        try:
                            if line_so_far:
                                line = raw_input(self.multiline_prompt)
                            else:
                                line = raw_input(self.prompt)
                        except EOFError:
                            line = 'exit'
                        except KeyboardInterrupt as ex:
                            line = ''
                            print
                            continue
                    else:
                        if line_so_far:
                            line = self.stdout.write(self.multiline_prompt)
                        else:
                            line = self.stdout.write(self.prompt)
                        self.stdout.flush()
                        line = self.stdin.readline()
                        if not len(line):
                            line = 'exit'
                        else:
                            line = line.rstrip('\r\n')

                # Ignore #! directive for unix
                if line.startswith("#!"):
                    continue

            #
            # added to ignore comments (ie. // and /* */ comments)
            #
                def comment_exists(comment, line):
                    found_pos = line.find(comment)
                    if found_pos != -1:
                        before_comment = line[:found_pos]
                        single_quotes_before = before_comment.count("'")
                        double_quotes_before = before_comment.count('"')
                        if double_quotes_before%2 == 1  or single_quotes_before%2 == 1:
                            found_pos = -1
                    return found_pos  

                # remove single line comments
                double_slash = comment_exists('//', line)
                if double_slash != -1 and line[double_slash-1]!="*":
                    line = line.partition('//')[0]

                # if multi-line comment had started
                if multi_comment:
                    multi_comment_pos = comment_exists('*/', line)
                    # if */ not found, skip this line
                    if multi_comment_pos == -1:
                        if line=="exit":
                           raise Exception("File ended before end of comment.")
                        else:
                            continue
                    else:
                        line = line.partition('*/')[2]
                        multi_comment = False

                multi_comment_start = comment_exists('/*', line)
                # loop is for lines like: /* comment */ blah /* more comments */
                while multi_comment_start != -1:
                    # if both /* and */ are on same line
                    multi_comment_end = comment_exists('*/', line)
                    if multi_comment_end != -1:
                        line = line[:line.find('/*')] + line[line.find('*/') + 2:]
                    else:
                        line = line.partition('/*')[0]
                        multi_comment = True
                    multi_comment_start = comment_exists('/*', line)

                # if line is empty, skip
                if not line.strip():
                    continue

            #
            # Added for multiline functionality
            #

                self.single_quotes += line.count("'")
                self.double_quotes += line.count('"')

                # set current_command if it was None
                if self.current_command is None and line.split():
                    self.current_command = line.split()[0]

                # if both quotes count is even but multiline has started (not through doc)
                if self.single_quotes + self.double_quotes != 0 \
                    and self.single_quotes % 2 == 0 \
                    and self.double_quotes % 2 == 0 and multiline_start \
                    and not self.doc_start:
                    line_so_far += line + '\n'
                    if line.strip() and line != prevline:
                        multi_count += 1
                elif multiline_start or line.count('<doc>') == 1 \
                    or self.single_quotes % 2 == 1 \
                    or self.double_quotes % 2 == 1:

                # set multiline_start to True if <doc> started, or quotes count is odd
                    if line.count('<doc>') == 1:
                        self.doc_start = True
                    line_so_far += line + '\n'
                    multiline_start = True
                    if line.strip() and line != prevline:
                        multi_count += 1
                    if line.count('</doc>') != 1:

                        # set prevline
                        prevline = line
                        continue

                # if line_so_far is not empty (multi-line)
                if line_so_far:
                    line = line_so_far.rstrip()
                    line_so_far = ''

                    # history modification
                    if used_rawinput:
                        history_length = readline.get_current_history_length()
                        # if history_length is not 0
                        if history_length:
                            # erase current history
                            for i in range(min(history_length, multi_count)):
                                readline.remove_history_item(history_length-i-1)

                            # add multi line
                            readline.add_history(line)

                # add line to history_log.txt
                if (line != 'exit' and line != prevline):
                    history = open(self.history_log_path).read().split('\n----------\n')
                    if len(history) > 50:
                        history = history[1:]
                    history = history[:-1]
                    history.append(line)
                    history = '\n----------\n'.join(history)
                    history += '\n----------\n'
                    open(self.history_log_path, 'w').writelines(history)

                # reset history
                multi_count = 0

            #
            # End of  multiline functionality
            #

                multiline_start = False

                self.current_command = None  # reset current_command
                self.single_quotes = 0
                self.double_quotes = 0
                self.doc_start = False

                # execute command
                try:
                    stop = self.start_command(line)
                except lb_exception.LBReportedException, ex:
                    if self.stop_on_error:
                        raise ex
                except lb_exception.LBExit, ex:
                    really_stop = True

                # set prevline to line
                prevline = line
                
            self.postloop()
        finally:
        # end loop
            if self.use_rawinput and self.completekey:
                try:
                    readline.set_completer(self.old_completer)
                except ImportError:
                    pass


class LbInteractiveTransaction(LbInteractive):
    """
    second REPL loop used for the transaction command
    instead of executing each command like LbInteractive, each command
    gets stored in a list
    """
    def __init__(
        self,
        stop_on_error=True,
        use_rawinput=True,
        stdout=None,
        stdin=None,
        cmdqueue=None,
        dev=False,
        current_directory=os.getcwd(),
        set_dict=None,
        ):
        cmd.Cmd.__init__(self, stdout=stdout, stdin=stdin)
        self.history_log_path = os.environ['HOME'] + '/.lb_history.txt';
        self.use_rawinput = use_rawinput
        self.dev = dev
        self.cmdqueue = cmdqueue
        self.current_directory = current_directory
        self.parser = dbcommands.lb_argparser.BuildLBInteractiveTransactionParser(self.current_directory).make()

        self.parser.formatter_class = cli.lbparser.LBHelpFormatter
        cli.lbparser.set_formatter(cli.lbparser.list_subparsers(self.parser))

        self.all_commands = self.parser._get_positional_actions()[0].choices.keys()

        # all input commands are stored here as parsed args
        self.transaction_commands_parsed = []
        self.transaction_commands_after_fixpoint_parsed = []
        self.echo_commands = []
        self.after_fixpoint = False
        self.identchars = string.ascii_letters + string.digits + '_' + ':'

        self.prompt = '>> '
        self.multiline_prompt = '>'

        self.do_not_abort = False
        self.stop_on_error = stop_on_error
        # set variables and values
        if set_dict is None:
            self.set_dict = {}
        else:
            self.set_dict = set_dict

        self.single_quotes = 0  # number of single quotes
        self.double_quotes = 0  # number of double quotes
        self.doc_start = False
        self.current_command = None  # stores current command (used for multiline)
        self.complete_command = None  # stores current command (used for tab completion)
        self.in_logic = False
        self.line_count = 0  # stores number of lines executed in current session

    def start_command(self, line):                
        line = self.precmd(line)
        return self.onecmd_wrapper(line)

    def default(self, line, split=True):
        """override default method. every command goes through this"""
        if split:
            line = self.split_arguments(line)
        args = self.parser.parse_args(line)

        # if a special function exists for that command, run it
        if args.func != 'default':
            return args.func(args, self)
        # otherwise, just add it to the list
        else:
            if self.after_fixpoint:
                self.transaction_commands_after_fixpoint_parsed.append(args)
            else:
                self.transaction_commands_parsed.append(args)

    def set_variables(self, cmdqueue=None, stdout=None, stdin=None, current_directory=None):
        """run before each transaction starts (make sure variable are same as interactive)"""
        if cmdqueue:
            self.cmdqueue = cmdqueue
        if stdout:
            self.stdout = stdout
        if stdin:
            self.stdin = stdin
        if current_directory:
            self.current_directory = current_directory
            self.parser.current_directory[0] = current_directory

    def clear_transaction_variables(self):
        """called after each transaction finished"""
        self.transaction_commands_parsed = []
        self.transaction_commands_after_fixpoint_parsed = []
        self.echo_commands = []
        self.cmdqueue = []
        self.after_fixpoint = False
        self.line_count = 0

    # Arguments echoed in a transaction get printed after a commit
    def do_echo(self, arg):
        self.echo_commands.append(arg)

    def do_assertCommitWouldFail(self, arg):
        self.set_dict["bloxunit:expectException"] = "Exception"
        return self.start_command("commit")

    def do_expectError(self, arg):
        self.set_dict["bloxunit:expectException"] = "Exception"
        self.do_not_abort = True
        self.start_command(arg)
