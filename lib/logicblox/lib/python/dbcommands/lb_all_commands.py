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
    This module contains functions that implement command line commands (i.e.,
    that are passed as a func argument to the parser), and also some helper
    functions.

    The convention is that functions starting with _ are local helpers.
"""


import sys, os, stat
from google.protobuf import text_format
import blox.connect.relations
import gzip
import StringIO
import time
import subprocess

import lb_command
from cli import lb_exception
from cli.util import Connection
from cli.util import print_utf8

from blox.connect.BloxCommand_pb2 import InputBinding
import blox.common.protobuf_json
import json

# debug mode can be set with an environment variable
LB_DEBUG='LB_DEBUG' in os.environ

# delta and unit are mysterious types which are not entities
primitive_preds = set(['int','float','string','decimal','datetime','boolean','delta','unit'])

def _get_conn(args):
    """
        @param args the command line arguments. This object must have isAdmin and unixDomainSocket attributes
        @return a new blox connect connection.
    """
    if args.isAdmin != None and args.isAdmin == True:
        conn = Connection(True, args.unixDomainSocket, hostname=args.hostname, port=args.admin_port or args.port)
    else:
        conn = Connection(False, args.unixDomainSocket, hostname=args.hostname, port=args.port)
    return conn

def _print_relation(rel, should_escape=True, csvFile=None, exclude_ids=False, delimiter=None):
    if delimiter is None:
        if csvFile is None:
            delimiter = ' '
        else:
            delimiter = ','
    printer = blox.connect.relations.RelationPrinter(rel)
    printer.escape_strings(should_escape)
    printer.entity_indexes(not exclude_ids)
    printer.delimiter = delimiter
    if csvFile == None:
        printer.output(sys.stdout)
    else:
        printer.output(csvFile)


def _print_problems(json_problems):
    if json_problems is None:
        return 0
    message="""
    %(code)s
    %(kind)s : %(message)s
    encountered from line %(startline)s, column %(startcolumn)s  to line %(endline)s, column %(endcolumn)s in block:%(block)s.
"""
    count = 0
    for warning in json_problems.warning:
        count += 1
        print message%{"code": warning.code,
                       "kind": "WARNING",
                       "message": warning.msg,
                       "startline": warning.position.start_line,
                       "startcolumn": warning.position.start_column,
                       "endline": warning.position.end_line,
                       "endcolumn": warning.position.end_column,
                       "block": warning.position.block_name
        }

    for error in json_problems.error:
        count += 1
        print message%{"code": error.code,
                       "kind": "ERROR",
                       "message": error.msg,
                       "startline": error.position.start_line,
                       "startcolumn": error.position.start_column,
                       "endline": error.position.end_line,
                       "endcolumn": error.position.end_column,
                       "block": error.position.block_name
        }
    return count



def _print_log(result):
    if hasattr(result, 'log') and result.log is not None:
        fileobj = gzip.GzipFile(fileobj=StringIO.StringIO(result.log))
        linenr = 0
        for line in fileobj:
            # This is a bit of a hack. Was trying to remove the == Log
            # Contents == header from lb-server, but this introduced
            # invalid gzip files because boost gzip compression is
            # broken if you do not write any data to the file
            # (https://svn.boost.org/trac/boost/ticket/5237). This was
            # a more pragmatic approach for now.
            if linenr == 0 and line.startswith("== Log"):
                continue
            print line,
            linenr = linenr + 1


def _print_result(result):
    _print_monitor_from_result(result)
    _print_log(result)
    if hasattr(result, 'output_relations'):
        for relation in result.output_relations:
            print "/--------------- %s ---------------\\" % relation[0]
            f = None
            if result.output_csv:
                print "Output written to %s.csv" % relation[0]
                f = open("%s.csv" % relation[0], 'w')

            delimiter = result.delimiter if result.delimiter else None
            _print_relation(relation[1], should_escape=result.should_escape, csvFile=f, exclude_ids=result.exclude_ids, delimiter=delimiter)
            print "\\--------------- %s ---------------/" % relation[0]

            if result.output_csv:
                f.close()


def _print_monitor_from_result(result):
    if hasattr(result, 'monitor_results'):
        for (pred, monitor_info) in result.monitor_results:
            (assertions, retractions) = monitor_info
            print '/--------------- +%s ---------------\\' % pred
            _print_relation(assertions,
                           should_escape = getattr(result,'should_escape',True))
            print '\\--------------- +%s ---------------/' % pred
            print '/--------------- -%s ---------------\\' % pred
            _print_relation(retractions,
                           should_escape = getattr(result,'should_escape',True))
            print '\\--------------- -%s ---------------/' % pred


def _print_transaction_result(results):
    """ prints out the output of transaction commands sequentially """

    #   iterate through all the commands
    #   attributes are based on protocol buffer
    def print_response(response):
        for result in response:
            result_method = getattr(sys.modules[__name__], '%s__print_result' % result.name)
            result_method(result)

    print_response(results.transaction_cmds)
    print_response(results.transaction_cmds_after_fixpoint)


def _get_workspaces(interactive):
    """Returns list of workspaces in the interactive object"""

    try:
        args = interactive.parser.parse_args(['workspaces'])
    except SystemExit:
        return

    conn = blox.connect.io.Connection(True)
    conn.open()

    cmd = lb_command.ListWorkspacesCommand.from_args(conn, args, interactive)
    result = cmd.run()
    return result.names


def _get_predicates(interactive):
    """Returns list of predicates of current workspace in the interactive object"""

    try:
        args = interactive.parser.parse_args(['list'])
    except SystemExit:
        return

    conn = blox.connect.io.Connection(False)
    conn.open()

    args.exclude = "(\$sip|\[.*\]|%|\$)"
    args.include = None
    args.predicate = None
    args.only_predicate_names = True
    cmd = lb_command.PredicatePopcountCommand.from_args(conn, args, interactive)
    result = cmd.run()

    predicate_names = []
    predicate_names = [p.qualified_name for p in result.pred_popcount.popcount]
    return predicate_names

def _get_blocks(interactive):
    """Returns list of blocks from current workspace in the interactive object"""

    try:
        args = interactive.parser.parse_args(['listblocks'])
    except SystemExit:
        return

    conn = blox.connect.io.Connection(False)
    conn.open()

    cmd = lb_command.ListInactiveBlocksCommand.from_args(conn, args, interactive)
    result = cmd.run()
    rel = result.blocks_relation
    for col in rel.column:
        values = getattr(col, 'string_column').values
        return values


def _get_options(command, interactive):
    """Returns list of options for the command of the interactive object"""

    options = []
    optionalactions = interactive.parser._get_positional_actions()[0].choices[command]._get_optional_actions()
    for optionalaction in optionalactions:
        for optionstring in optionalaction.option_strings:
            options.append(optionstring)
    return options


def version(args, interactive=None):
    """Print version"""

    conn = _get_conn(args).open()
    cmd = lb_command.VersionCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_log(result)

    if not args.detail:
        print '%s.%s' % (result.version, result.minor_version)
    else:
        print '%s.%s.%s' % (result.version, result.minor_version, result.build_number)


def print_list_workspaces(args, interactive=None):
    """
        Prints a list of all workspaces
    """
    for name in get_list_workspaces(args, interactive):
        print name


def get_list_workspaces(args, interactive=None):
    """
        Execute the connectblox command to list workspaces. Return a list with their names.
    """
    args.isAdmin = True
    conn = _get_conn(args).open()
    cmd = lb_command.ListWorkspacesCommand.from_args(conn, args, interactive)
    return cmd.run().names


def filepath_workspace(args, interactive=None):
    """Prints the filepath of the workspace"""

    conn = _get_conn(args).open()
    cmd = lb_command.WorkspaceFilepathCommand.from_args(conn, args, interactive)
    result = cmd.run()
    print result.filepath


def create_workspace(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.CreateWorkspaceCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print "created workspace '%s'" % result.workspace_name
    if interactive:
        workspace = result.workspace_name

        # update current workspace
        interactive.set_curr_workspace(workspace)

        # update list of workspaces
        interactive.update_workspaces()

def parse_branch_bindings(line):
    """
      Parses this line of branch bindings and returns a list of the BindBranchAlias
      objects created. A line should be a comma separated list of assignments,
      e.g.: _input1=foo, _input2=bar. 
    """
    bindings = []
    for assignment in line.split(','):
        key_value = assignment.split('=')
        if len(key_value) != 2:
            raise lb_exception.LBCommandArgsError("invalid list of branch binding assignments")
        binding = blox.connect.BloxCommand_pb2.BindBranchAlias()
        binding.alias = key_value[0].strip()
        binding.branch_name = key_value[1].strip()
        bindings.append(binding)
    return bindings

def execute_block(args, interactive=None):
    def _parse_input_bindings(line):
        """
            Parses this line of input bindings and returns a list of the InputBinding
            objects created. A line should be a comma separated list of assignments,
            e.g.: _input1=foo, _input2=bar. All inputs are considered a single string,
            i.e. it is currently not possible to input multiple values or types different
            than string.
        """
        bindings = []
        for assignment in line.split(','):
            key_value = assignment.split('=')
            if len(key_value) != 2:
                raise lb_exception.LBCommandArgsError("invalid list of input binding assignments")
            ib = InputBinding()
            ib.name = key_value[0].strip()
            ib.relation.column.add().string_column.values.append(key_value[1].strip())
            bindings.append(ib)
        return bindings

    # if "input" contains an assignment line, parse and create the "inputs" for bindings.
    if hasattr(args, 'input') and isinstance(args.input, basestring):
        args.inputs = _parse_input_bindings(args.input)
    if hasattr(args, 'bind_branch') and isinstance(args.bind_branch, basestring):
        args.branch_bindings = parse_branch_bindings(args.bind_branch)
    conn = _get_conn(args).open()
    cmd = lb_command.ExecuteBlockCommand.from_args(conn, args, interactive)
    result = cmd.run()
    exec_inactive__print_result(result)


def exec_inactive__print_result(result):
    _print_result(result)


def execute_logic(args, interactive=None):
    conn = _get_conn(args).open()
    if hasattr(args, 'bind_branch') and isinstance(args.bind_branch, basestring):
        args.branch_bindings = parse_branch_bindings(args.bind_branch)
    cmd = lb_command.ExecuteLogicCommand.from_args(conn, args, interactive)
    result = cmd.run()
    exec__print_result(result)


def exec__print_result(result):
    _print_result(result)
    _print_problems(result.errors)


def query_logic(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.QueryLogicCommand.from_args(conn, args, interactive)
    result = cmd.run()
    exec__print_result(result)


def delete_workspace(args, interactive=None):
    """Deletes a list of workspaces"""

    conn = _get_conn(args).open()
    names = args.name
    for name in names:
        args.name = name
        cmd = lb_command.DeleteWorkspaceCommand.from_args(conn, args, interactive)
        result = cmd.run()
        _print_result(result)
        print "deleted workspace '%s'" % args.name

        # if deleted is current workspace, close
        if interactive and interactive.current_workspace == args.name:
            interactive.set_curr_workspace('')

    # update list of workspaces
    if interactive:
        interactive.update_workspaces()

def export_workspace(args, interactive=None):
    command_args = [
        os.path.expandvars('$LOGICBLOX_HOME/bin/dlbatch'), '-command', 'hotcopy',
        '--workspace', args.name,
        '--dest', args.dest
        ]

    if args.hostname is not None:
        command_args += [ '--hostname', args.hostname ]
    if args.port is not None:
        command_args += [ '--port', args.port ]
    else:
        conn = _get_conn(args)
        if (hasattr(conn, 'port')):
            command_args += [ '--port', str(conn.port) ]
    if args.overwrite:
        command_args += [ '--overwrite' ]
    if args.unixDomainSocket is not None:
        command_args += [ '--uxdomain', args.unixDomainSocket ]

    # Currently ignores exit code, matching behavior for lb services
    # Once a better solution arises, we should set it properly
    try:
        subprocess.check_call(command_args)
        print "exported workspace '%s' to directory '%s'" % (args.name, args.dest)
    except subprocess.CalledProcessError:
        raise lb_exception.LBCommandError("export-workspace '%s' to directory '%s' failed" % (args.name, args.dest))

def import_workspace(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ImportWorkspaceCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print "imported workspace '%s'" % result.name


def predicate_info(args, interactive=None):
    """Prints a dictionary of predicate attributes"""
    conn = _get_conn(args).open()
    if (not args.all) and len(args.name) == 1:
        cmd = lb_command.PredicateInfoCommand.from_args(conn, args, interactive)
    else:
        cmd = lb_command.PredicateInfoBulkCommand.from_args(conn, args, interactive)
    result = cmd.run()
    pred_info__print_result(result)


def pred_info__print_result(result):
    _print_result(result)
    print result.pred_info


def print_list_predicates(args, interactive=None):
    """
        Print the result of listing predicates.
    """
    _print_pred_info_as_list(list_predicates(args, interactive))

def get_list_predicates(args, interactive=None):
    """
        Get the list of predicates and return as a list of names.
    """
    result = list_predicates(args, interactive)
    # print the sorted list of names
    predicate_names = []
    predicate_names = [p.qualified_name for p in result.pred_popcount.popcount]
    for name in sorted(predicate_names):
        yield name

def list_predicates(args, interactive=None):
    """
        Execute the list predicates connectblox command and return the
        connectblox response.
    """
    # We implement list via popcount and exclude special predicates
    # special are:
    #   predicates ending in $sip
    #   predicates with square brackets in their name
    #   predicates with a % in their name (nonce predicates)
    #   any other predicates with a $ in their name
    conn = _get_conn(args).open()
    args.exclude = "(\$sip|\[.*\]|%|\$)"
    args.include = None
    args.predicate = None
    args.only_predicate_names = True
    cmd = lb_command.PredicatePopcountCommand.from_args(conn, args, interactive)
    return cmd.run()

def _print_pred_info_as_list(result):
    # Is implemented via popcount without requesting the actual counts
    _print_monitor_from_result(result)
    if hasattr(result, 'log') and result.log is not None:
        fileobj = gzip.GzipFile(fileobj=StringIO.StringIO(result.log))
        for line in fileobj:
            print line,
    # print the sorted list of names
    predicate_names = []
    predicate_names = [p.qualified_name for p in result.pred_popcount.popcount]
    for name in sorted(predicate_names):
        print name

def predicate_density(args, interactive=None):
    conn = _get_conn(args).open()
    # The predicates we want density for
    pred_set = set()
    if args.name is not None:
        pred_set.update(args.name)
    if args.predicate is not None:
        pred_set.update(args.predicate)
    # run Popcount command to get predicates included in regexp
    # and popcount for the queried predicates
    popcounts = {}
    cmd = lb_command.PredicatePopcountCommand.from_args(conn, args, interactive)
    result = cmd.run()
    for p in result.pred_popcount.popcount:
        popcounts[p.qualified_name] = p.popcount
        pred_set.add(p.qualified_name)

    #get keyspaces
    predinfo_cmd = lb_command.PredicateInfoBulkCommand([p for p in pred_set],args.workspace,False)
    result = predinfo_cmd.run()
    pred_infos = result.pred_info_message.info
    augmented_set = set()
    predinfo_dict = {}
    for info in pred_infos:
        predinfo_dict[info.name] = info
        for k in info.key_argument:
            if k not in primitive_preds:
                augmented_set.add(k)
    args.name = augmented_set
    
    #call popcount again to get population of keys
    cmd = lb_command.PredicatePopcountCommand.from_args(conn, args, interactive)
    result = cmd.run()
    for pc in result.pred_popcount.popcount:
        popcounts[pc.qualified_name] = pc.popcount
    for pred in pred_set:
        if predinfo_dict[pred].is_calculated:
            continue
        if predinfo_dict[pred].qualified_name in primitive_preds:
            continue

        max_pop = 1
        for k in predinfo_dict[pred].key_argument:
            if k in popcounts: # this is an entity
                max_pop = max_pop * popcounts[k]
            else:              # this is a builtin density is NA
                max_pop = 0

        if max_pop>0:
            print "%10d %5d%% %s"%(popcounts[pred], 100*popcounts[pred]/max_pop, pred)
        else:
            print "%10d %s %s"%(popcounts[pred],"    NA", pred)



def predicate_popcount(args, interactive=None):
    if args.density:
        predicate_density(args, interactive=interactive)
    else:
        conn = _get_conn(args).open()
        cmd = lb_command.PredicatePopcountCommand.from_args(conn, args, interactive)
        result = cmd.run()
        _print_log(result)
        pred_popcount = [(p.qualified_name, p.popcount)
                        for p in result.pred_popcount.popcount]
        for qualified_name,popcount in pred_popcount:
            print "%10d: %s" % (popcount, qualified_name)

def create_branch(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.CreateBranchCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_log(result)

def replace_default_branch(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.DefaultBranchCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_log(result)

def delete_branch(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.DeleteBranchCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_log(result)

def list_branches(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ListBranchesCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_log(result)
    return cmd.run().names

def print_list_branches(args, interactive=None):
    for name in list_branches(args, interactive):
        print name

def get_list_branches(args, interactive=None):
    """
        Get the list of branches and return as a list of names.
    """
    return sorted(list_branches(args, interactive))

def list_blocks(args, interactive=None):
    '''
        Use execute_batch_script to get blocks list.
    '''
    if args.inactive and not args.active:
        script = 'summary --kind INERT_BLOCKS --lifetime database'
    elif not args.inactive and args.active:
        script = 'summary --kind BLOCKS --lifetime database'
    else:
        script = '''
            echo Active Blocks:
            summary --kind BLOCKS --lifetime database
            echo
            echo Inactive Blocks:
            summary --kind INERT_BLOCKS --lifetime database
        '''
    args.transactional = True
    args.script = script
    args.file = None
    execute_batch_script(args, interactive=interactive)

def print_block(args, interactive=None):
    '''
        Use execute_batch_script to print block.
    '''
    script = "printBlock -B %s"%args.block
    args.transactional = True
    args.script = script
    args.file = None
    execute_batch_script(args, interactive=interactive)

def print_rules(args, interactive=None):
    '''
        Use execute_batch_script to print block.
    '''
    script = " showDefiningRules --predicate %s"%args.predicate
    if args.internal:
        script = "%s --internal"%script
    args.transactional = True
    args.script = script
    args.file = None
    execute_batch_script(args, interactive=interactive)


def query_predicate__print_result(result):
    _print_result(result)
    _print_relation(result.predicate_relation,
                    should_escape = getattr(result,'should_escape',True),
                    exclude_ids = getattr(result,'exclude_ids',False),)

def print_predicate(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.PrintPredicateCommand.from_args(conn, args, interactive)
    result = cmd.run()
    query_predicate__print_result(result)

def add_block__print_result(result):
    _print_result(result)
    _print_problems(result.errors)
    print "added block '%s'" % result.block_name


def add_block(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.AddBlockCommand.from_args(conn, args, interactive)
    result = cmd.run()
    add_block__print_result(result)

def compile_block(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.CompileBlockCommand.from_args(conn, args, interactive)
    result = cmd.run()
    compile_block__print_result(result)


def compile_block__print_result(result):
    _print_problems(result.errors)
    _print_result(result)


def replace_block(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ReplaceBlockCommand.from_args(conn, args, interactive)
    result = cmd.run()
    replace_block__print_result(result)


def replace_block__print_result(result):
    _print_result(result)


def remove_block(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.RemoveBlockCommand.from_args(conn, args, interactive)
    result = cmd.run()
    remove_block__print_result(result)


def remove_block__print_result(result):
    if (_print_problems(result.errors) == 0):
        if len(result.block_names) == 1:
            print "removed block '%s'" % result.block_names[0]
        else:
            print "removed blocks '%s'" % ', '.join(result.block_names)


def add_library(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.AddLibraryCommand.from_args(conn, args, interactive)
    result = cmd.run()
    install_library__print_result(result)


def install_library__print_result(result):
    _print_result(result)


def add_project(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.AddProjectCommand.from_args(conn, args, interactive)
    result = cmd.run()
    install_project__print_result(result)


def install_project__print_result(result):
    _print_result(result)



def insert_log_message(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.InsertLogMessageCommand.from_args(conn, args, interactive)
    result = cmd.run()
    log_message__print_result(result)


def log_message__print_result(result):
    _print_result(result)


def import_protobuf(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ImportProtobufCommand.from_args(conn, args, interactive)
    result = cmd.run()
    import_protobuf__print_result(result)


def import_protobuf__print_result(result):
    print 'Protobuf message imported'


def export_protobuf(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ExportProtobufCommand.from_args(conn, args, interactive)
    result = cmd.run()
    export_protobuf__print_result(result)


def export_protobuf__print_result(result):
    print 'Protobuf message exported'


def proto_add_spec(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ProtoAddSpecCommand.from_args(conn, args, interactive)
    result = cmd.run()
    proto_add_spec__print_result(result)


def proto_add_spec__print_result(result):
    print 'Protobuf message descriptor has been imported'

def proto_get_descriptors(args):
    conn = _get_conn(args).open()
    cmd = lb_command.GetProtocolDescriptorsCommand.from_args(conn, args)
    result = cmd.run()

def xml_add_spec(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.XMLAddSpecCommand.from_args(conn, args, interactive)
    result = cmd.run()
    xml_add_spec__print_result(result)


def xml_add_spec__print_result(result):
    _print_result(result)


def import_xml_doc(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ImportXMLCommand.from_args(conn, args, interactive)
    result = cmd.run()
    import_xml_doc__print_result(result)

def raw_request(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.RawCommand(conn, args, interactive)
    cmd.run()

def import_xml_doc__print_result(result):
    _print_result(result)


def shutdown(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ShutdownCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print result.message
    return True

def server_loglevel(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ServerLoglevelCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print result.message

def abort_transaction(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.AbortTransactionCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print result.res

def check_status(args, interactive=None):

    try:
        conn = _get_conn(args).open()
        cmd = lb_command.CheckStatusCommand.from_args(conn, args, interactive)
        result = cmd.run()
    # could not connect to lb-server, this is an expected exception
    # print to stdout and return 1, as expected by lb-services
    except lb_exception.LBServerOff as off_error:
        print off_error
        return 1
    # something else went wrong, throw an exception
    except Exception as e:
        raise lb_exception.LBServerOff("lb-server: {0}".format(e.strerror))

    print "lb-server is running."

    answeredWorkspaces = []
    if len(result.res.status.workspaces):
       print "---"

    for ws in result.res.status.workspaces:
       answeredWorkspaces.append(ws.name)

       if ws.num_requests == -1:
          print "Workspace '%s' is closed." % (ws.name)
       elif ws.num_requests == 0:
          print "Workspace '%s' is idle." % (ws.name)
       else:
          print "Workspace '%s' is processing" % (ws.name), ws.num_requests, "request(s)."

       for req in ws.requests:
          print text_format.MessageToString(req)

       for info in ws.debug_info:
          print info

    for ws in cmd.workspaces:
       if ws not in answeredWorkspaces:
         print "Workspace '%s' does not exist." % (ws)

    if len(result.res.status.debug_info):
       print "---"
    for info in result.res.status.debug_info:
       print info,


def info(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.GetWorkspaceInfoCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    if not result.info.IsInitialized():
        raise lb_exception.LBCommandAPIException('Did not get valid server response.')
    if args.json:
        print json.dumps(blox.common.protobuf_json.protobuf_to_dict(result.info),indent=4)
    else:
        print str(result.info).rstrip() # FIXME: print nicer



def start_mirror(args, interactive=None):
    args.remote_workspace = args.remote_workspace or args.name
    conn = _get_conn(args).open()
    cmd = lb_command.StartMirrorCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)

    if interactive:
        interactive.set_curr_workspace(args.name)
        interactive.update_workspaces()


def stop_mirror(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.StopMirrorCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)


def promote_mirror(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.PromoteMirrorCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)


def copy_remote(args, interactive=None):
    args.remote_workspace = args.remote_workspace or args.name
    conn = _get_conn(args).open()
    cmd = lb_command.CopyRemoteWorkSpaceCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)

def extract_example(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ExtractExampleCommand.from_args(conn, args, interactive)
    result = cmd.run()

    outdir = args.outdir

    for rel in result.returned_data:
       if rel.name == "_files_":
          for fnum in range(len(rel.column[0].string_column.values)):
              fname = rel.column[0].string_column.values[fnum]
              fname = os.path.join(outdir, fname)
              dirname = os.path.dirname(fname)
              try:
                  os.makedirs(dirname)
              except Exception as e:
                  pass
              with open(fname, "w") as f:
                  f.write(rel.column[1].string_column.values[fnum])
              if os.path.basename(fname) == 'example.sh':
                  st = os.stat(fname)
                  os.chmod(fname, st.st_mode | stat.S_IEXEC)
    _print_result(result)

def execute_batch_script(args, interactive=None):
    conn = _get_conn(args).open()
    cmd = lb_command.ExecuteBatchScriptCommand.from_args(conn, args, interactive)
    result = cmd.run()
    _print_result(result)
    print_utf8(result.output)
 
    for rel in result.returned_data:
       if rel.name == "_files_":
          for fnum in range(len(rel.column[0].string_column.values)):
              fname = rel.column[0].string_column.values[fnum]
              dirname = os.path.dirname(fname)
              try:
                  os.makedirs(dirname)
              except Exception as e:
                  pass
              with open(fname, "w") as f:
                  f.write(rel.column[1].string_column.values[fnum])
      
    result


def starttimer(args, interactive):
    interactive.timer = time.time()

def elapsedtime(args, interactive):
    """Prints the time elapsed from the previous starttimer,
        or the beginning of session if no starttimer is run"""

    conn = _get_conn(args).open()
    seconds_fmt = '%.5f' % (time.time() - interactive.timer)
    if args.message:
        print(' '.join([seconds_fmt if t == "#TIME#" else t for t in args.message]))
    else:
        print(seconds_fmt)


def set_var(args, interactive):
    """Set a variable to a value, also used for expectException"""

    conn = _get_conn(args).open()
    if args.value is None:
        if '=' not in args.variable:
            raise lb_exception.ArgumentParserError("Argument not set correctly. \
                Please use 'set VAR VALUE' or 'set VAR=VALUE'")
        else:
            (args.variable, separator, args.value) = args.variable.partition('=')
    interactive.set_dict[args.variable] = args.value


def interactive_exit(args, interactive):
    raise lb_exception.LBExit(0)

def transaction(args, interactive):
    """Starts a REPL that handles transaction commands.
        Commands are all run at commit"""

    conn = _get_conn(args).open()
    # check workspace is open
    if interactive.current_workspace in interactive.list_workspaces:
        transaction_loop = interactive.transaction

        # give this transaction variables that it needs
        transaction_loop.set_variables(cmdqueue=interactive.cmdqueue,
                stdout=interactive.stdout, stdin=interactive.stdin,
                current_directory=interactive.current_directory)
        interactive.in_transaction = True

        try:
            transaction_loop.cmdloop()  # starts the REPL
        finally:
            # add in line count for errors
            interactive.line_count += transaction_loop.line_count

        interactive.in_transaction = False
        cmds = transaction_loop.transaction_commands_parsed
        cmds_after_fixpoint = transaction_loop.transaction_commands_after_fixpoint_parsed
        try:
            if cmds or cmds_after_fixpoint:

                args.workspace = interactive.current_workspace
                args.commands = cmds
                args.commands_after_fixpoint = cmds_after_fixpoint
                cmd = lb_command.TransactionCommand.from_args(conn, args, interactive)
                result = cmd.run()
                _print_transaction_result(result)

        finally:
            # even if exception is raised, clear all commands, line_count, cmdqueue
            transaction_loop.clear_transaction_variables()

    else:
        raise lb_exception.LBCommandError('No workspace open.')


def save(args, interactive):
    """Saves commands to a file. Can specify the number of lines to save"""

    conn = _get_conn(args).open()
    import readline
    start = 1
    end = readline.get_current_history_length()
    option = 'a'
    fileloc = args.file

    # make file name end in .lb
    if not fileloc[-3:] == '.lb':
        fileloc += '.lb'

    # if -n argument (number of lines)
    if args.n != -1 and int(args.n) < end:
        start = end - int(args.n)

    # if overwrite argument
    if args.overwrite:
        option = 'w'

    writefile = open(fileloc, option)
    for i in range(start, end):
        writefile.write('%s\n' % readline.get_history_item(i))
    writefile.close()
    print '%d commands saved to %s' % (end - start, fileloc)


def open_workspace(args, interactive):
    """Saves a workspace to the session. Required for commands using workspace"""

    conn = _get_conn(args).open()
    workspace = args.workspace
    list_workspace = _get_workspaces(interactive)
    if workspace in list_workspace:
        interactive.current_workspace = workspace
        interactive.prompt = 'lbi %s> ' % workspace
    else:
        raise lb_exception.LBCommandError("workspace %s does not exist. Use command 'workspaces' for an existing list of workspaces" % workspace)

def close(args, interactive):
    """Remove the saved workspace"""
    # if no workspace is open
    conn = _get_conn(args).open()

    if not interactive.current_workspace:
        raise lb_exception.LBCommandError("No workspace open.")
    if args.destroy:
        args.name = [str(interactive.current_workspace)]
        delete_workspace(args, interactive)
    interactive.current_workspace = ''
    interactive.prompt = interactive.default_prompt

def log_level(args, interactive):
    """sets log level (without checking that it's valid) """
    interactive.loglevel = args.loglevel
    conn = _get_conn(args).open()


def source(args, interactive):
    """Runs commands in a file using cmdqueue as input"""
    try:
        conn = _get_conn(args).open()

        sourced_file = args.file
    except IOError, ex:
        print ex
        return
    from interactive import lb_interactive_console
    # create new interactive object
    source_interactive = lb_interactive_console.LbInteractive(
                                    stdout=StringIO.StringIO(),
                                    stdin=interactive.stdin,
                                    cmdqueue=None,
                                    dev=interactive.dev,
                                    set_dict=interactive.set_dict)
    source_interactive.set_current_directory(os.path.abspath(os.path.dirname(sourced_file.name)))
    source_interactive.cmdqueue = sourced_file.readlines() + ["exit"]
    source_interactive.set_curr_workspace(interactive.current_workspace)
    # run sourced commands
    source_interactive.cmdloop()
    interactive.set_curr_workspace(source_interactive.current_workspace)

def transaction_commit(arg, interactive):
    for to_echo in interactive.echo_commands:
        print to_echo
    raise lb_exception.LBExit(42)

def transaction_abort(arg, interactive):
    if interactive.do_not_abort:
        return transaction_commit(arg, interactive)
    interactive.transaction_commands_parsed = []
    if 'bloxunit:expectException' in interactive.set_dict:
        interactive.set_dict.pop('bloxunit:expectException')
    raise lb_exception.LBExit(42)

def transaction_fixpoint(arg, interactive):
    if interactive.after_fixpoint:
        raise lb_exception.LBCommandError('Commands are already after fixpoint!')
    else:
        interactive.after_fixpoint = True

def transaction_set_var(args, interactive):
    """Handles set commands inside a transaction"""

    if args.value is None:
        if '=' not in args.variable:
            raise lb_exception.ArgumentParserError("Argument not set correctly. \
                Please use 'set VAR VALUE' or 'set VAR=VALUE'")
        else:
            (args.variable, separator, args.value) = args.variable.partition('=')

    interactive.set_dict[args.variable] = args.value


def transaction_exit(args, interactive):
    interactive.transaction_commands_parsed = []
    raise lb_exception.LBExit(42)
