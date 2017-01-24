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

import argparse
import os
import lb_all_commands
from cli import lb_exception
from cli import util
from cli.completers import *

"""
lb_argparse separates the argparser found in lb_main and lb_interactive_console into 4 distinct argparsers:
  1. add_transaction_commands - includes all lb_main commands that are available in a transaction
  2. add_base_commands - includes all lb_main commands that are not in add_transaction_commands
  3. add_interactive_commands - includes all commands available in the interactive shell and transactions
  4. add_interactive_only_commands - includes all commands only available in the interactive shell not including transactions
  5. add_transaction_only_commands - includes commands only available within a transaction


lb_main uses 1 and 2
LbInteractive uses 1, 2, 3, and 4
LbInteractiveTransaction uses 1,3, and 5
"""

class LBArgumentParser(argparse.ArgumentParser):
    """Modified Argument Parser class for Interactive and Interactive Transaction"""

    # commands in interactive that require a workspace
    exclude_commands = ['open']

    # arguments of commands in interactive that should be excluded
    exclude_arguments = ['workspace']

    def __init__(self, prog=None, current_directory=None):
        if current_directory:
            self.current_directory = current_directory
        else:
            self.current_directory = [os.getcwd()]
        super(LBArgumentParser, self).__init__(prog=prog)

    def error(self, message):
        """Raises ArgumentParserError instead of writing to stderr and SysExit"""

        if self.prog:
            raise lb_exception.ArgumentParserError('%s: %s\n'
                    % (self.prog, message))
        else:
            raise lb_exception.ArgumentParserError('%s\n' % message)

    def parse_args(self, args=None, namespace=None):
        """Returns the parsed arguments with current directory appended to dir arguments"""

        (args, argv) = self.parse_known_args(args, namespace)
        if 'dir' in args:
            args.dir = os.path.join(self.current_directory[0], args.dir)
        if argv:
            msg = argparse._('unrecognized arguments: %s')
            self.error(msg % ' '.join(argv))
        return args

    def _get_value(self, action, arg_string):
        """Appends the current directory to file names then runs default _get_value"""

        if action.type.__class__ is argparse.FileType:
            arg_string = os.path.join(self.current_directory[0],
                    arg_string)
        return super(LBArgumentParser, self)._get_value(action,
                arg_string)

    def _parse_optional(self, arg_string):
        """Checks if square or round parentheses is in argument, if yes, it is a positional argument"""
        # options do not have parenthesis. This was meant to be logic
        if '(' in arg_string or '[' in arg_string:
            return None

        return super(LBArgumentParser, self)._parse_optional(arg_string)

    def _check_value(self, action, value):
        # converted value must be one of the choices (if specified)
        if action.choices is not None and value not in action.choices:
            tup = value, ', '.join(map(repr, action.choices))
            msg = argparse._('invalid choice: %r') % tup[0]
            raise argparse.ArgumentError(action, msg)

    def add_argument(self, *args, **kwargs):
        """Ignores arguments listed in exclude_arguments if they are required"""

        # Arguments in interactive that require a workspace to be entered are added
        if self.prog.strip() in self.exclude_commands:
            super(LBArgumentParser, self).add_argument(*args, **kwargs)

        # Arguments that are not in exclude_arguments are added
        elif args[0] not in self.exclude_arguments:
            super(LBArgumentParser, self).add_argument(*args, **kwargs)


        # Arguments in exclude_arguments that are optional are added
        elif 'nargs' in kwargs and kwargs['nargs'] == '?':
            super(LBArgumentParser, self).add_argument(*args, **kwargs)

        return self


class BuildLBMainParser(object):
    """class to crate an ArgumentParser object for lb_main"""

    def make(self, parser, subparsers):
        """Returns a default ArgumentParser object"""
        parser.add_argument(
            '-u', "--unix-domain-socket",
            action="store",
            dest="unixDomainSocket",
            metavar='FILE',
            default=None,
            help="connect via a unix domain socket on a given path")

        parser.add_argument('--hostname', help='host name of server', default=None)
        parser.add_argument('--port', help='port the server is listening on', default=None)
        parser.add_argument('--admin-port', help='admin port the server is listening on', default=None)

        # subparsers = self.parser.add_subparsers(title='commands')
        self.add_base_commands(subparsers)
        self.add_transaction_commands(subparsers)
        return parser

    def add_general_arguments(self, parser):
        """Adds common arguments"""
        parser.add_argument('--loglevel',
                            help='log level to change to. ' + util.get_log_levels())
        parser.add_argument('-L', '--log',
                            action='store_true',
                            help='transfer log from server and print')
        parser.set_defaults(isAdmin=False)
        parser.add_argument('--cwd',
                            nargs='?',
                            const=os.getcwd(),
                            metavar='DIR',
                            help="use current working directory. Used to resolve file predicate paths")

    def add_transaction_arguments(self, parser, read_only_option=True):
        """Adds arguments for all requests that are transactions"""
        parser.add_argument('--timeout', '-t',
                            help='transaction timeout (in milliseconds)',
                            type=int)

        parser.add_argument('--exclusive',
                            action='store_true',
                            help='set this flag if this request should be the only one running in the workspace')

        parser.add_argument('--commit-mode',
                            choices=['softcommit', 'diskcommit'],
                            help='set to either softcommit or diskcommit')

        parser.add_argument('--branch',
                            nargs='?',
                            metavar='NAME',
                            help='named workspace branch to use for transaction')

        parser.add_argument('-m', '--monitor',
                            action='append',
                            metavar='PREDICATE',
                            help='print assertions and retractions for predicate at end of transaction')

        if read_only_option:
            parser.add_argument('--readonly',
                            action='store_true',
                            help='execute this command in a read-only transaction')

    def add_exec_arguments(self,parser, read_only_option=True):
            parser.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
            group = parser.add_mutually_exclusive_group(required=True)
            group.add_argument('logic', nargs='?', help='logic to add. If logic starts with a \'-\', please use \'--\' before the logic to get correct parsing behavior')
            group.add_argument('-f', '--file', type=argparse.FileType('r'), help='logic file to execute')
            parser.add_argument('--raw',
                            action='store_false',
                            dest='escape',
                            help='print query result without escaping')
            parser.add_argument('--exclude-ids', action='store_true', dest='exclude_ids', help='output only refmode values of entities')
            parser.add_argument('--csv', action='store_true', dest='output_csv', help='print query result to csv files')
            parser.add_argument('--delimiter', help='delimiter when printing query result to csv files')
            parser.add_argument('--print', action="append", metavar="PRED", nargs="?", help="print local predicate PRED. Default '_'")
            parser.add_argument('--language', default='lb', action='store', help="source language of block: lb (default) or lb0")
            self.add_general_arguments(parser)
            self.add_transaction_arguments(parser, read_only_option = read_only_option)

    def add_base_commands(self, subparsers):
        """Adds commands that are not available in a transaction"""

        # version
        p = subparsers.add_parser('version', help='print version')
        p.add_argument('workspace', help='name of workspace', nargs='?').completer = WorkspaceCompleter
        p.add_argument('-d', '--detail',
                        default=False,
                        action='store_true',
                        help='print detailed version')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.version)

        # list workspaces
        p = subparsers.add_parser('workspaces', help='list workspaces')
        self.add_general_arguments(p)
        p.set_defaults(isAdmin=True)
        p.set_defaults(func=lb_all_commands.print_list_workspaces)

        # filepath
        p = subparsers.add_parser('filepath', help='find file system path of workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('-i', '--inverse',
                        default=False,
                        action='store_true',
                        help='find workspace name from path of workspace')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.filepath_workspace)

        # create workspace
        p = subparsers.add_parser('create', help='create new workspace')
        p.add_argument('name', nargs='?', help='name or prefix of the new workspace')
        p.add_argument('--unique', action='store_true', help='create a workspace with a unique name')
        p.add_argument('--overwrite', action='store_true', help='delete existing workspace with the same name, if it exists')
        p.add_argument('--libs', help='comma separated list of libs to load')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.create_workspace)

        # import workspace
        p = subparsers.add_parser('import-workspace', help='import existing unmanaged workspace')
        p.add_argument('name', nargs='?', help='name or prefix of the new workspace')
        p.add_argument('src', help='location of unmanaged workspace to import')
        p.add_argument('--unique', action='store_true', help='create a workspace with a unique name')
        p.add_argument('--overwrite', action='store_true', help='delete existing workspace with the same name, if it exists')

        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.import_workspace)

        # delete workspace
        p = subparsers.add_parser('delete', help='delete workspace')
        p.add_argument('name', nargs='+', help='name of workspace to delete', metavar='NAME').completer = WorkspaceCompleter
        p.add_argument('-f', '--force', action='store_true', help='ignore non-existent workspaces')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.delete_workspace)

        # export workspace
        p = subparsers.add_parser('export-workspace', help='export workspace')
        p.add_argument('name', help='name of workspace to export').completer = WorkspaceCompleter
        p.add_argument('dest', help='destination (file path)')
        p.add_argument('--overwrite', action='store_true', help='overwrite if the destination already exists')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.export_workspace)

        # branch
        p = subparsers.add_parser('branch', help='create a new named branch')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', metavar='branch', help='name of new branch')
        p.add_argument('--parent', help='branch to create new named branch from, if not default').completer = BranchCompleter
        p.add_argument('--overwrite', '-o', action='store_true', help='overwrite if the branch already exists')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.create_branch)

        # branches
        p = subparsers.add_parser('branches', help='list named branches')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('--all', action='store_true', help='also list branches created for automatic backups')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.print_list_branches)

        # replace-default-branch
        p = subparsers.add_parser('replace-default-branch', help='replace current version of default branch by the current version of the given branch')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', metavar='branch', help='name of the branch')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.replace_default_branch)

        # delete-branch
        p = subparsers.add_parser('delete-branch', help='delete named branch')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', metavar='branch', help='name of branch to delete').completer = BranchCompleter
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.delete_branch)

        # list blocks
        p = subparsers.add_parser('list-blocks', help='list blocks in a workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        group = p.add_mutually_exclusive_group(required=False)
        group.add_argument('--inactive', action='store_true', help='list only inactive blocks')
        group.add_argument('--active', action='store_true', help='list only active blocks')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.list_blocks)

        # print block
        p = subparsers.add_parser('print-block', help='print the logic for a block')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('block', help='name of block')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.print_block)

        # print defining rules
        p = subparsers.add_parser('print-rules', help='print the rules defining a predicate')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('predicate', help='name of predicate').completer = PredicateCompleter
        p.add_argument('--internal', action='store_true', help='also print internal rules')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.print_rules)

        # Abort transaction
        p = subparsers.add_parser('aborttransaction', help='abort a transaction')
        p.add_argument('workspace', help='workspace', action='store', nargs='?').completer = WorkspaceCompleter
        p.add_argument('tid', help='transaction id')
        p.set_defaults(isAdmin=True)
        p.set_defaults(func=lb_all_commands.abort_transaction)

        # Server status
        p = subparsers.add_parser('status', help='server status')
        p.add_argument('--active', help='show active requests', action='store_true')
        p.add_argument('--all', help='show all requests (active and queued)', action='store_true')
        p.add_argument('--debug', help='show debug details', action='store_true')
        p.add_argument('workspace', help='workspace(s) to be queried', action='store', nargs='*').completer = WorkspaceCompleter
        p.set_defaults(isAdmin=True)
        p.set_defaults(func=lb_all_commands.check_status)

        # info
        p = subparsers.add_parser('info', help='print information about a workspace')
        p.add_argument('name', help='name of the workspace').completer = WorkspaceCompleter
        p.add_argument('--json', action='store_true', help='print information in JSON format')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.info)

        # start-mirror
        p = subparsers.add_parser('start-mirror', help='start or resume mirroring a remote workspace')
        p.add_argument('name', help='name of the local workspace').completer = WorkspaceCompleter
        p.add_argument('host', help='host name of the remote LogicBlox server')
        p.add_argument('--remote-workspace', default=None, help='name of the remote workspace')
        p.add_argument('--remote-port', default=5518, type=int, help='port of the remote LogicBlox server')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.start_mirror)

        # stop-mirror
        p = subparsers.add_parser('stop-mirror', help='stop mirroring a remote workspace')
        p.add_argument('name', help='name of the local workspace').completer = WorkspaceCompleter
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.stop_mirror)

        # promote-mirror
        p = subparsers.add_parser('promote-mirror', help='promote a mirror workspace to master')
        p.add_argument('name', help='name of the local workspace').completer = WorkspaceCompleter
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.promote_mirror)

        # copy-remote
        p = subparsers.add_parser('copy-remote', help='make a copy of a remote workspace')
        p.add_argument('name', help='name of the local workspace').completer = WorkspaceCompleter
        p.add_argument('host', help='host name of the remote LogicBlox server')
        p.add_argument('--remote-workspace', default=None, help='name of the remote workspace')
        p.add_argument('--remote-port', default=5518, type=int, help='port of the remote LogicBlox server')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.copy_remote)

        # extract-example
        p = subparsers.add_parser('extract-example', help='Generate code for isolating small examples')
        p.add_argument('name', help='name of the source workspace').completer = WorkspaceCompleter
        p.add_argument('--predicate', help='predicate to generate logic for', required = True)
        p.add_argument('--outdir', default='.', help='directory for generated logic and scripts')
        p.add_argument('--transitive', action='store_true', help='transitively include all rules reachable from specified predicates')
        p.add_argument('--monitor', action='store_true', help='generate logic to monitor changes to predicates')
        p.add_argument('--defun', action='append', help='remove functional dependencies on the specified predicates')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.extract_example)

        # dlbatch script
        p = subparsers.add_parser('batch-script', help='execute a dlbatch script on the server')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('-t', '--transactional', default=False, action='store_true', help='execute commands inside a transaction')
        p.add_argument('-r', '--return-data', default=False, action='store_true', help='return data created by server')
        group = p.add_mutually_exclusive_group(required=True)
        group.add_argument('script', nargs='?', help='script commands to be executed')
        group.add_argument('-f', '--file', type=argparse.FileType('r'), help='file containing script commands to execute')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.execute_batch_script)


    def add_transaction_commands(self, subparsers):
        """Adds commands available in a transaction"""

        # print facts
        p = subparsers.add_parser('print', help='print facts of predicate')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', help='name of predicate').completer = PredicateCompleter
        p.add_argument('--exclude-ids', action='store_true', dest='exclude_ids', help='output only refmode values of entities')
        p.add_argument('--raw', action='store_false', dest='should_escape', help='print results without escaping')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p, read_only_option=False)
        p.set_defaults(func=lb_all_commands.print_predicate)

        # predinfo
        p = subparsers.add_parser('predinfo', help='print information about predicate')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', nargs="*", action="store", help="name of predicate").completer = PredicateCompleter
        p.add_argument('--all', action='store_true', help="return info for all user-predicates. [Deprecated]")
        self.add_general_arguments(p)
        self.add_transaction_arguments(p, read_only_option=False)
        p.set_defaults(func=lb_all_commands.predicate_info)

        # list predicates
        p = subparsers.add_parser('list', help='list predicates in workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        self.add_general_arguments(p)
        self.add_transaction_arguments(p, read_only_option=False)
        p.set_defaults(func=lb_all_commands.print_list_predicates)

        # predicate popcount
        p = subparsers.add_parser('popcount', help='print popcount for all, or specified, predicates')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', nargs="*", action="store", help="name of predicate").completer = PredicateCompleter
        p.add_argument('-p', '--predicate',
                        action='append',
                        metavar='PREDICATE',
                        help='print popcount for specific predicate')
        p.add_argument('-i', '--include', nargs='?', action='store', help="regular expression [Perl-syntax] for predicates to include")
        p.add_argument('-e', '--exclude', nargs='?', action='store', help="regular expression [Perl-syntax] for predicates to exclude")
        p.add_argument('-d', '--density', action='store_true', help="print density when available")
        p.add_argument('--estimate', action='store_true', help='print estimated rather than actual size')
        p.add_argument('--include-default', action='store_true', help='for default-valued predicates, use size of default layer')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p, read_only_option=False)
        p.set_defaults(func=lb_all_commands.predicate_popcount)

        # execute an inactive block
        p = subparsers.add_parser('execblock', help='execute inactive block and optionally print results')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', help='name of inactive block to execute')
        p.add_argument('--raw', action='store_false', dest='escape', help='print query result without escaping')
        p.add_argument('--exclude-ids', action='store_true', dest='exclude_ids', help='output only refmode values of entities')
        p.add_argument('--csv', action='store_true', dest='output_csv', help='print query result to csv files')
        p.add_argument('--delimiter', help='delimiter when printing query result to csv files')
        p.add_argument('--print', action="append", metavar="PRED", nargs="?", help="print local predicate PRED. Default '_'")
        p.add_argument('--input', help='string with a list of bindings for local variables in the block. Only strings are supported. Example: \'_in1=string1, _in2=string2\'')
        p.add_argument('--bind-branch', dest="bind_branch", help='string with a list of branch bindings. Example: \'branch1=x123, branch2=y456\'')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.execute_block)

        # execute logic
        p = subparsers.add_parser('exec', help='execute logic and optionally print results')
        p.add_argument('--blockname', help='name of block')
        p.add_argument('--bind-branch', dest="bind_branch", help='string with a list of branch bindings. Example: \'branch1=x123, branch2=y456\'')
        p.set_defaults(func=lb_all_commands.execute_logic)
        self.add_exec_arguments(p)

        # query
        p = subparsers.add_parser('query', help='execute logic and print results')
        p.set_defaults(func=lb_all_commands.query_logic)
        self.add_exec_arguments(p, read_only_option=False)

        # add block
        p = subparsers.add_parser('addblock', help='add active or inactive block to workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('logic', nargs='?', help='logic to add')
        p.add_argument('-f', '--file', type=argparse.FileType('r'), help='logic file to add')
        p.add_argument('--name', help='name of block (default: unique name)')
        p.add_argument('--inactive', action='store_false', dest='active', help='add block as inactive block')
        p.add_argument('--language', default='lb', action='store', help="source language of block: lb (default) or lb0")
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.add_block)

        # compile block
        p = subparsers.add_parser('compileblock', help='test compiling active or inactive block')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('logic', nargs='?', help='logic to compile')
        p.add_argument('-f', '--file', type=argparse.FileType('r'), help='logic file to compile')
        p.add_argument('--name', help='name of block (default: unique name)')
        p.add_argument('--inactive', action='store_false', dest='active', help='active or inactive block')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.compile_block)

        # add library
        p = subparsers.add_parser('addlib', help='add library to workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', help='name of library to add')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.add_library)

        # add project
        p = subparsers.add_parser('addproject', help='add project to workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('dir', help='project directory path')
        p.add_argument('--norecurse', default=False, action='store_true', help='avoid finding libraries recursively')
        p.add_argument('--nocopy', default=False, action='store_true', help='skip copy of level 1 workspace')
        p.add_argument('--libpath', default='', help='the path for lb libraries that this project depends on')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.add_project)

        # remove block
        p = subparsers.add_parser('removeblock', help='remove a block from the workspace')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('blockname', help='name of block to remove', nargs='+')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.remove_block)

        # replace block
        ## disable until NRT supports this
        # p = subparsers.add_parser('replace-block', help='replace a block in the workspace')
        # p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        # p.add_argument('blockname', help='name of block to replace')
        # p.add_argument('--logic', help='logic to add into the block')
        # p.add_argument('-f', '--file', type=argparse.FileType('r'), help='logic file to add into the block')
        # self.add_general_arguments(p)
        # p.set_defaults(func=lb_all_commands.replace_block)


        # add log trace
        p = subparsers.add_parser('insert-log-message', help='insert a message in the log')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('message', help='message text')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.insert_log_message)

        # import protobuf
        p = subparsers.add_parser('import-protobuf', help='import protobuf message from a file')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('protocol', help='name of the protocol to use')
        p.add_argument('msgType', help='protobuf message type of the data file')
        p.add_argument('file', type=argparse.FileType('r'), help='protobuf message data file')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.import_protobuf)

        # export protobuf
        p = subparsers.add_parser('export-protobuf', help='export protobuf message to a file')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('protocol', help='name of the protocol to use')
        p.add_argument('msgType', help='protobuf message type of the data file')
        p.add_argument('file', type=argparse.FileType('w'), help='protobuf message data file')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.export_protobuf)

        # protobuf add spec
        p = subparsers.add_parser('import-protobuf-schema', help='protobuf add specification from a file')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', help='name of message protocol to add')
        p.add_argument('file', type=argparse.FileType('r'), help='protobuf message descriptor file')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.proto_add_spec)

        # protobuf query installed descriptors
        p = subparsers.add_parser('export-protobuf-schema', help="get installed protocol descriptors")
        p.add_argument('--protocol',
           action="append",
           metavar="PROTOCOL",
           help="save descriptor for selected protocols. Multiple OK")
        p.add_argument('-i', '--include', nargs='?', action='store', help="regular expression of protocol names to include")
        p.add_argument('-e', '--exclude', nargs='?', action='store', help="regular expression of protocol names to exclude")
        p.add_argument('workspace', help="name of workspace").completer = WorkspaceCompleter
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.proto_get_descriptors)

        # add XML schema
        p = subparsers.add_parser('import-xml-schema', help='add XML schema specification from a file')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('name', help='name for the schema')
        p.add_argument('file', type=argparse.FileType('r'), help='binary schema descriptor file, generated by importexport')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.xml_add_spec)

        # import XML
        p = subparsers.add_parser('import-xml', help='import XML document')
        p.add_argument('workspace', help='name of workspace').completer = WorkspaceCompleter
        p.add_argument('--schema', default=None, help='name of schema (optional)')
        p.add_argument('file', type=argparse.FileType('r'), help='the /path/to/XML/file')
        self.add_general_arguments(p)
        self.add_transaction_arguments(p)
        p.set_defaults(func=lb_all_commands.import_xml_doc)

        # raw request
        p = subparsers.add_parser('raw', help='send raw request to server [for debugging]')
        p.add_argument('request', help='string representation of Request message')
        p.add_argument('-v', '--verbose', help='print Request and Response', default=False, action='store_true')
        p.add_argument('--is-admin', help='admin-request', default=False, action='store_true', dest='isAdmin')
        p.set_defaults(func=lb_all_commands.raw_request)

class BuildLBInteractiveParser(BuildLBMainParser):

    """class to create an LBArgumentParser object for lb_interactive"""

    def __init__(self, current_directory=os.getcwd()):
        # Current directory is a list so that it may be passed by reference
        # the overriden ArgumentParser object is created here
        self.parser = LBArgumentParser(prog='',
                current_directory=[current_directory])

    def make(self):
        """Returns a LBArgumentParser object"""

        self.parser.set_defaults(unixDomainSocket=None, hostname=None, port=None, admin_port=None)

        subparsers = self.parser.add_subparsers(title='commands')
        self.add_base_commands(subparsers)
        self.add_transaction_commands(subparsers)
        self.add_interactive_commands(subparsers)
        self.add_interactive_only_commands(subparsers)
        self.modify_interactive_commands(subparsers)
        return self.parser

    def modify_interactive_commands(self, subparsers):
        """Sets the current_directory of subparsers of the parser by reference"""

        for command in subparsers.choices.values():
            command.current_directory = self.parser.current_directory

    def add_base_commands(self, subparsers):
        """Calls the base class method"""

        super(BuildLBInteractiveParser,
              self).add_base_commands(subparsers)

    def add_transaction_commands(self, subparsers):
        """Calls the base class method"""

        super(BuildLBInteractiveParser,
              self).add_transaction_commands(subparsers)

    def add_interactive_commands(self, subparsers):
        """Adds commands available in interactive and transaction"""

        # loglevel
        p = subparsers.add_parser('loglevel', help='change loglevel')
        p.add_argument('loglevel', help='loglevel to change to ' + util.get_log_levels())
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.log_level)

        p = subparsers.add_parser('help', help='print this list of commands and their descriptions')
        def print_help(args, interactive):
            print self.parser.format_help()
        p.set_defaults(func=print_help)

    def add_interactive_only_commands(self, subparsers):
        """Adds commands only available within the interactive shell but not transactions"""
        #Note: if the command requires a workspace argument, add the command to LBArgumentParser's exclude_command attribute

        # open
        p = subparsers.add_parser('open', help='open a workspace')
        p.add_argument('workspace', help='name of workspace')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.open_workspace)

        # close
        p = subparsers.add_parser('close', help='close a workspace')
        p.add_argument('-D', '--destroy', action='store_true',
                       help='delete the current workspace as close')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.close)

        # start timer
        p = subparsers.add_parser('starttimer', help='start timer')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.starttimer)

        # elapsed time
        p = subparsers.add_parser('elapsedtime', help='output elapsed time since starttimer command')
        p.add_argument('message', nargs='*', default=None)
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.elapsedtime)

        # set
        p = subparsers.add_parser('set', help="use either 'set VAR VALUE' or 'set VAR=VALUE'")
        p.add_argument('variable', help='variable name or VAR=VALUE')
        p.add_argument('value', nargs='?', default=None)
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.set_var)

        # exit
        p = subparsers.add_parser('exit', help='exit interactive shell')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.interactive_exit)

        # save
        p = subparsers.add_parser('save', help='save all previous commands to file')
        p.add_argument('file', help="file to append to (create file if doesn't exist)")
        p.add_argument('-n', default=-1, help='number of previous commands to save')
        p.add_argument('--overwrite', '-o', action='store_true', help='truncate file instead of appending')
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.save)

        # echo
        p = subparsers.add_parser('echo', help='print argument')
        p.add_argument('argument', nargs='+', help='to print')
        p.set_defaults(isAdmin=False)

        # source .lb script
        p = subparsers.add_parser('source', help='run another .lb script in this context')
        p.add_argument('file', type=argparse.FileType('r'), help='file to source')
        self.add_general_arguments(p)
        p.set_defaults(func=lb_all_commands.source)

        # transaction
        p = subparsers.add_parser('transaction', help='start a transaction')
        p.add_argument('--timeout', '-t', default=-1, help='maximum number of milliseconds a transaction is allowed to run for. The value -1 defines infinite time is allowed')
        p.add_argument('--exclusive',
                       default=False,
                       action='store_true',
                       help='makes this transaction exclusive')
        p.add_argument('--readonly',
                       default=False,
                       action='store_true',
                       help='makes this transaction read-only')
        p.add_argument('--branch',
                       nargs='?',
                       metavar='NAME',
                       help='named workspace branch to use for transaction').completer = BranchCompleter

        # add_general_arguments(p)
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.transaction)

class BuildLBInteractiveTransactionParser(BuildLBInteractiveParser):

    """class to create an LBArgumentParser object for Transactions in lb_interactive"""

    def __init__(self, current_directory=os.getcwd()):
        self.parser = LBArgumentParser(prog='',
                current_directory=[current_directory])

    def make(self):
        """Returns an LBArgumentParser object"""

        subparsers = self.parser.add_subparsers(title='commands')
        self.add_interactive_commands(subparsers)
        self.add_transaction_commands(subparsers)
        self.add_transaction_only_commands(subparsers)
        return self.parser

    def modify_transaction_commands(self, subparsers):
        """Sets the current_directory of subparsers of the parser
        by reference and adds a cmd argument"""

        # Use superclass method
        self.modify_interactive_commands(subparsers)

        # Add cmd argument that stores a class name in lb_command
        # so that it may be used by TransactionCommand
        for command in subparsers.choices.values():
            if 'func' in command._defaults:
                command.set_defaults(cmd=self.get_command_class(command._defaults['func']))
                command.set_defaults(func='default')

    def add_interactive_commands(self, subparsers):
        """Calls base class method"""

        super(BuildLBInteractiveTransactionParser,
              self).add_interactive_commands(subparsers)
        super(BuildLBInteractiveTransactionParser,
              self).modify_interactive_commands(subparsers)

    def add_transaction_commands(self, subparsers):
        """Calls base class method"""

        super(BuildLBInteractiveTransactionParser,
              self).add_transaction_commands(subparsers)
        self.modify_transaction_commands(subparsers)

    def get_command_class(self, key):
        """Maps commands to their classes in lb_command"""

        func_to_class = {
            lb_all_commands.predicate_info: 'PredicateInfo',
            lb_all_commands.execute_block: 'ExecuteBlock',
            lb_all_commands.execute_logic: 'ExecuteLogic',
            lb_all_commands.query_logic: 'QueryLogic',
            lb_all_commands.add_block: 'AddBlock',
            lb_all_commands.compile_block: 'CompileBlock',
            lb_all_commands.add_library: 'AddLibrary',
            lb_all_commands.add_project: 'AddProject',
            lb_all_commands.remove_block: 'RemoveBlock',
            lb_all_commands.replace_block: 'ReplaceBlock',
            lb_all_commands.insert_log_message: 'InsertLogMessage',
            lb_all_commands.import_protobuf: 'ImportProtobuf',
            lb_all_commands.export_protobuf: 'ExportProtobuf',
            lb_all_commands.proto_add_spec: 'ProtoAddSpec',
            lb_all_commands.xml_add_spec: 'XMLAddSpec',
            lb_all_commands.import_xml_doc: 'ImportXML',
            lb_all_commands.print_predicate: 'PrintPredicate'
            }
        try:
            return func_to_class[key]
        except KeyError:
            return key

    def add_transaction_only_commands(self, subparsers):
        """Adds commands only available in a transaction"""

        p = subparsers.add_parser('commit', help='commit all commands in transaction to workspace')
        p.set_defaults(func=lb_all_commands.transaction_commit)

        p = subparsers.add_parser('abort', help='abort all commands in transaction')
        p.set_defaults(func=lb_all_commands.transaction_abort)

        p = subparsers.add_parser('fixpoint', help='set marker to begin inserting commands after fixpoint')
        p.set_defaults(func=lb_all_commands.transaction_fixpoint)

        p = subparsers.add_parser('echo', help='print argument')
        p.add_argument('argument', nargs='+', help='to print')

        p = subparsers.add_parser('set', help="use either 'set VAR VALUE' or 'set VAR=VALUE'")
        p.add_argument('variable', help='variable name or VAR=VALUE')
        p.add_argument('value', nargs='?', default=None)
        p.set_defaults(isAdmin=False)
        p.set_defaults(func=lb_all_commands.transaction_set_var)

        p = subparsers.add_parser('exit', help='exit out of transaction')
        p.set_defaults(func=lb_all_commands.transaction_exit)
