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
from __future__ import print_function

import sys
import os
import getpass
import urlparse
import subprocess
import signal

import lb.web.admin
import lb.web.batch
import lb.web.credentials

from cli import lb_exception
from cli import util

from web import util as webutil

import blox.connect.ConnectBlox_pb2 as cb
import blox.connect.io as io
import lb.web.service
import json
from workbook_api import WorkbookManager
from workbook_api import WorkbookException
from urlparse import urlparse

def add_workbook_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(title='workbook commands')

    # Use better formatter for commands, and use the standard of
    # invoking the function cmd_{subcommand}
    def add_command(cmd, help):
        p = more_subparsers.add_parser(cmd, help=help)
        fun = globals()['cmd_' + cmd.replace('-', '_')]
        p.set_defaults(func=fun)
        return p

    p = add_command('create', help="create a workbook")
    p.add_argument('-j', '--json', dest="json", help="workbook specification json file")
    p.add_argument('-v', '--verbose', action = "store_true", help="show instantiated workbook specification")

    p = add_command('delete', help="delete a workbook")
    p.add_argument('-w', '--workspace', help="workspace",required=True)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',   dest='workbook_id',   help="delete workbook with specified id", nargs="*")
    g.add_argument('--name', dest='workbook_name', help="delete workbooks with specified name")
    g.add_argument('--all',                        help="delete all workbooks", action="store_true")

    p = add_command('list', help="list workbooks")
    p.add_argument('-w', '--workspace', help="workspace", required="true")
    p.add_argument('--output', help="level of detail needed (default: abbrev)", choices=['abbrev', 'id_only', 'verbose'])
    p.add_argument('--csv', nargs='+', help="space-separated list of workbook fields to print as csv")
    p.add_argument('--delimiter', default="|", help='delimiter when printing query result to csv files')
    g = p.add_mutually_exclusive_group()
    g.add_argument('--id',         dest='workbook_id',   help="list only workbooks with specified id")
    g.add_argument('--name',       dest='workbook_name', help="list only workbooks with specified name")
    # on purpose not in mutual exclusion group
    p.add_argument('-u', '--user', dest='user_id',       help="list only workbooks for this user")
    p.add_argument('-t', '--template-name', dest='template_name',       help="list only workbooks for template with specified template-name")
    p.add_argument('--include-deleted', action = "store_true", help="include deleted workbooks")

    p = add_command('create-template', help="create template")
    p.add_argument('-w', '--workspace', help="workspace", required=True)
    p.add_argument('-j', '--json', dest="json", help="template specification json file")

    p = add_command('list-templates', help="list templates")
    p.add_argument('-w', '--workspace', help="workspace", required=True)
    p.add_argument('--csv', nargs='+', help="print specified fields as csv output")
    p.add_argument('--delimiter', default="|", help='delimiter when printing query result to csv files')
    g = p.add_mutually_exclusive_group()
    g.add_argument('--id',   dest='template_id',   help="list template with the specified id")
    g.add_argument('--name', dest='template_name', help="list templates with the specified name")

    p = add_command('delete-template', help="delete template")
    p.add_argument('-w', '--workspace', help="workspace", required=True)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',   dest='template_id',   help="delete template with the specified id")
    g.add_argument('--name', dest='template_name', help="delete templates with the specified name")
    g.add_argument('--all',                        help="delete all templates", action="store_true")

    p = add_command('instantiate', help="instantiate template")
    p.add_argument('-w', '--workspace', help="workspace", required=True)
    p.add_argument('-j', '--json', dest="json", help="template instantiation json file")
    p.add_argument('-v', '--verbose', action = "store_true", help="show instantiated workbook specification")

    p = add_command('commit', help="commit")
    p.add_argument('-w', '--workspace', help="master workspace", required=True)
    p.add_argument('-g', '--group', help="name of commit group", default="default")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',   dest='workbook_id',   help="workbook id")
    g.add_argument('--name', dest='workbook_name', help="commit workbooks with given name")
    g.add_argument('--all',                        help="commit all workbooks", action="store_true")

    p = add_command('refresh', help="refresh")
    p.add_argument('-w', '--workspace', help="master workspace", required=True)
    p.add_argument('-g', '--group', help="name of refresh group", default="default")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',   dest='workbook_id',   help="workbook id")
    g.add_argument('--name', dest='workbook_name', help="refresh workbooks with given name")
    g.add_argument('--all',                        help="refresh all workbooks", action="store_true")

    p = add_command('addusers', help="(deprecated) use add-users")
    p.add_argument('-w', '--workspace', help="master workspace", required=True)
    p.add_argument('-u', '--users', nargs='+', help="users list")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',    dest='workbook_id',   help="workbook id")
    g.add_argument('--name',  dest='workbook_name', help="workbook name")

    p = add_command('add-users', help="add users")
    p.add_argument('-w', '--workspace', help="master workspace", required=True)
    p.add_argument('-u', '--users', nargs='+', help="users list")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',    dest='workbook_id',   help="workbook id")
    g.add_argument('--name',  dest='workbook_name', help="workbook name")


    p = add_command('delete-users', help="delete users")
    p.add_argument('-w', '--workspace', help="master workspace", required=True)
    p.add_argument('-u', '--users', nargs='+', help="users list")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--id',    dest='workbook_id',   help="workbook id")
    g.add_argument('--name',  dest='workbook_name', help="workbook name")

def find_workbooks(manager, args):
    # note: we can just ignore the all flag.
    wbs = manager.list(workbook_name=args.workbook_name, workbook_id=args.workbook_id)

    # only raise an error if the option '--all' is not used
    if len(wbs) == 0:
        if args.workbook_id is not None:
            raise lb_exception.LBCommandError("workbook '%s' not found" % args.workbook_id)
        if args.workbook_name is not None:
            raise lb_exception.LBCommandError("workbook '%s' not found" % args.workbook_name)

    return wbs

def cmd_commit(args):
    manager = WorkbookManager(args.workspace)
    wbs  = find_workbooks(manager, args)
    payload = json.dumps({"name": args.group})
    for wb in wbs:
        print("committing workbook '%s'" % wb.id(), file=sys.stderr)
        message = json.loads(manager.commit(wb.id(), payload))
        if 'errors' in message:
            for e in message['errors']:
                print("Warning:"+e)

def cmd_refresh(args):
    manager = WorkbookManager(args.workspace)
    wbs  = find_workbooks(manager, args)
    payload = json.dumps({"name": args.group})
    for wb in wbs:
        print("refreshing workbook '%s'" % wb.id(), file=sys.stderr)
        message = json.loads(manager.refresh(wb.id(), payload))
        if 'errors' in message:
            for e in message['errors']:
                print("Warning:"+e)


def cmd_create(args):
    try:
        spec_string = open(args.json).read()
        spec = json.loads(spec_string)
        workspace = spec['parent_workbook']['workspace_name']
        manager = WorkbookManager(workspace)
        wb = manager.create(spec_string)
        if(args.verbose):
            pretty_print(json.dumps(wb.json))
        print("created workbook with id '%s'" % wb.id(), file=sys.stderr)
    except Exception as e:
        print("Failed to create workbook:\n%s" % e, file=sys.stderr)
        sys.exit(1)

def cmd_delete(args):
    manager = WorkbookManager(args.workspace)
    if args.all:
        msg = json.loads(manager.delete_all())
    else:
        if args.workbook_name:
            wbs  = find_workbooks(manager, args)
            ids = [wb.id() for wb in wbs]
        else:
            ids = args.workbook_id
        print("Deleting "+",".join(ids))
        msg = json.loads(manager.delete(ids))

    if('deleted' in msg):
        print("Deleted %s"%",".join([id for id in msg['deleted']]))
    if('already_deleted' in msg):
        print("%s was/were already deleted "%",".join([id for id in msg['already_deleted']]))
    if('not_found' in msg):
        print("%s was/were not found "%",".join([id for id in msg['not_found']]))




def cmd_list(args):
    manager = WorkbookManager(args.workspace)

    # We're not using find_workbooks because we do not want to fail if
    # there are no workbooks.
    wbs = manager.list(workbook_name=args.workbook_name,
                       workbook_id=args.workbook_id,
                       output=args.output,
                       include_deleted=args.include_deleted,template_name=args.template_name)

    if args.csv != None:
        import csv
        writer = csv.writer(sys.stdout, delimiter=args.delimiter, quotechar="\"", lineterminator="\n")
        # TODO add support for template_name
        for wb in wbs:
            writer.writerow([wb.json.get(v, None) for v in args.csv])
    else:
        pretty_print(json.dumps([wb.json for wb in wbs]))

def cmd_create_template(args):
    manager = WorkbookManager(args.workspace)
    try:
        wbt = manager.create_template(open(args.json).read())
        print("created template with id '%s'" % wbt.id(), file=sys.stderr)
    except WorkbookException as ex:
        print(str(ex))
        sys.exit(1)

def cmd_list_templates(args):
    manager = WorkbookManager(args.workspace)
    result = manager.list_templates(template_name=args.template_name, template_id=args.template_id)
    if args.csv != None:
        import csv
        writer = csv.writer(sys.stdout, delimiter=args.delimiter, quotechar="\"", lineterminator="\n")
        for wbt in result:
            writer.writerow([wbt.json[v] for v in args.csv])
    else:
        for wbt in result:
            pretty_print(json.dumps(wbt.json))

def cmd_delete_template(args):
    manager = WorkbookManager(args.workspace)

    # note: we can just ignore the all flag.
    templates = manager.list_templates(template_name=args.template_name, template_id=args.template_id)

    # only raise an error if the option '--all' is not used
    if len(templates) == 0:
        if args.template_id is not None:
            raise lb_exception.LBCommandError("template '%s' not found" % args.template_id)
        if args.template_name is not None:
            raise lb_exception.LBCommandError("template '%s' not found" % args.template_name)

    for wbt in templates:
        print("deleting template '%s'" % wbt.id(), file=sys.stderr)
        manager.delete_template(wbt.id())

def cmd_instantiate(args):
    manager = WorkbookManager(args.workspace)
    try:
        wb = manager.instantiate(open(args.json).read())
        if(args.verbose):
            pretty_print(json.dumps(wb.json))
        else:
            print("created workbook with id '%s'" % wb.id(), file=sys.stderr)
    except WorkbookException as ex:
        print(str(ex))
        sys.exit(1)


def cmd_addusers(args):
    print("WARNING: (deprecated) use add-users instead of addusers")
    cmd_add_users(args)


def cmd_add_users(args):
    manager = WorkbookManager(args.workspace)
    result = manager.addusers(args.users,
                              workbook_id=getattr(args,"workbook_id",None),
                              workbook_name=getattr(args,"workbook_name",None))

def cmd_delete_users(args):
    manager = WorkbookManager(args.workspace)
    result = manager.deleteusers(args.users,
                              workbook_id=getattr(args,"workbook_id",None),
                              workbook_name=getattr(args,"workbook_name",None))

def pretty_print(json_string):
    print(json.dumps(json.loads(json_string), indent=2, sort_keys=True))
