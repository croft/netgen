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

import dbcommands.lb_argparser

def add_commands(parser, subparsers):
    dbcommands.lb_argparser.BuildLBMainParser().make(parser, subparsers)


def get_db_commands_list():
    '''
        Returns a list with the names of all commands created by the dbcommands parser. This is used
        to create a section for these commands in the help. We have to try to keep it in sync when 
        we develop new commands or rename them.
    '''
    return [
          'aborttransaction',
          'addblock',
          'addlib',
          'addproject',
          'branch',
          'branches',
          'compileblock',
          'create',
          'start-mirror',
          'stop-mirror',
          'promote-mirror',
          'delete',
          'delete-branch',
          'exec',
          'execblock',
          'export',
          'export-protobuf',
          'export-workspace',
          'filepath',
          'import',
          'import-protobuf',
          'import-workspace',
          'import-xml',
          'insert-log-message',
          'list',
          'list-blocks',
          'popcount',
          'predinfo',
          'print',
          'print-block',
          'print-rules',
          'import-protobuf-schema',
          'export-protobuf-schema',
          'query',
          'raw',
          'removeblock',
          'replaceblock',
          'status',
          'version',
          'workspaces',
          'import-xml-schema',
          'info',
          'copy-remote',
          'batch-command'
    ]
