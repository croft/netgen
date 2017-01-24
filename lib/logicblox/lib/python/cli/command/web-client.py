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

import web.webclient
import cli.util
import cli.lb_exception
import functools
import sys

not_installed_message = 'WARNING: Web client is not installed. Please install and set environment variable LB_WEBCLIENT_HOME.'

def add_commands(parser, subparsers):
    """
        Add this command to the main parser.
    """

    ## assuming this module is in /logicblox/lib/python/cli, look in:
    ## - ../../.. since we can have lb-web-client installed together with logicblox
    ## - ../../../../lb-web-client
    ## - /opt/logicblox/lb-web-client
    candidates = ['../../..', '../../../../lb-web-client', '/opt/logicblox/lb-web-client']

    ## LB_WEBCLIENT_HOME needs the following files:
    ## config/lb-web-client.config and lb-web-client.jar ando ther jar files in lib/java
    lb_web_client_files = [
        'config/lb-web-client.config',
        'lib/java/lb-web-client.jar'
    ]

    web_client_home = cli.util.find_home(candidates, lb_web_client_files, ['LB_WEBCLIENT_HOME', 'LB_WEBSERVER_HOME'])
    subparser = subparsers.add_parser(
        'web-client', help='logiQL web-client%s' % ' (not installed)' if not web_client_home else '',
        description=not_installed_message if not web_client_home else None)

    if web_client_home:
        web_client_subparsers = subparser.add_subparsers(title='web-client commands')

        BatchCommand(web_client_subparsers, web_client_home).add_commands()
        ExportDelimCommand(web_client_subparsers, web_client_home).add_commands()
        ImportDelimCommand(web_client_subparsers, web_client_home).add_commands()
        ImportCredentialsCommand(web_client_subparsers, web_client_home).add_commands()
        CallCommand(web_client_subparsers, web_client_home).add_commands()
        BcryptCommand(web_client_subparsers, web_client_home).add_commands()
        HomeDirCommand(web_client_subparsers, web_client_home).add_commands()

        '''
        p = web_client_subparsers.add_parser('home-dir', help="print the directory used for LB_WEBCLIENT_HOME")
        def print_home(args):
            print web_client_home
        p.set_defaults(func=print_home)
        '''
    else:
        subparser.set_defaults(extra_func=no_webclient)


def no_webclient(args, extra, command_line):
    raise cli.lb_exception.LBServerOff(not_installed_message)

def _lb_web_client(lb_webclient_home, args, extra, command_line):
    #print >> sys.stderr, 'Assuming %s is installed at %s\n' % ('lb web-client', lb_webclient_home)
    web.webclient.run(args, command_line[1:], lb_webclient_home)


## below is a copy of java client Main.java class, translated to python argparse

class WebClientCommand(object):
    desc = ''

    def __init__(self, subparsers, home):
        self.parser = subparsers.add_parser(self.name, description=self.desc, help=self.desc)
        call_lb_web_client = functools.partial(_lb_web_client, home)
        self.parser.set_defaults(extra_func=call_lb_web_client)

    def add_commands(self):
        self.parser.add_argument('--config', help='custom configuration file, overriding defaults')

class BatchCommand(WebClientCommand):
    name = 'batch'
    desc = 'execute a batch script'

    def add_commands(self):
        super(BatchCommand, self).add_commands()

        self.parser.add_argument('-i', '--input', metavar='FILE', help='batch input file (default: read from standard input)')
        self.parser.add_argument('--json',action = 'store_true', help='use JSON for batch specifications')
        self.parser.add_argument('-o', '--output', metavar='FILE', help='batch output file')

class ExportDelimCommand(WebClientCommand):
    name = 'export'
    desc = 'export a delimited file'

    def add_commands(self):
        super(ExportDelimCommand, self).add_commands()

        self.parser.add_argument('Service-URI', help='the service URI to connect to')
        self.parser.add_argument('-t', '--transport', help='transport configuration section')
        self.parser.add_argument('-n', '--no-compression', action='store_true', help='do not use GZIP compression on the wire')
        self.parser.add_argument('-o', '--output', metavar='FILE', help='output file or S3 URL')
        self.parser.add_argument('-T', '--timeout', help='the server timeout (in seconds for the request')
        self.parser.add_argument('-k', '--key', help='the name of the encryption key to encrypt the file in S3')

class ImportDelimCommand(WebClientCommand):
    name = 'import'
    desc = 'import a delimited file'

    def add_commands(self):
        super(ImportDelimCommand, self).add_commands()

        self.parser.add_argument("Service-URI", help='the service URI to connect to')
        self.parser.add_argument("-t", "--transport", help="transport configuration section")
        self.parser.add_argument("-n", "--no-compression", action='store_true', help='do not use GZIP compression on the wire')
        self.parser.add_argument("-f", "--full", action='store_true', help="input is a full replacement for existing data")
        self.parser.add_argument("-b", "--ignore-bad-records", action='store_true', help="do not return the bad records from the import")
        self.parser.add_argument("-i", "--input", metavar='FILE', help="input file or S3 URL to import")
        self.parser.add_argument("-o", "--output", metavar='FILE', help="output file or S3 URL to store error file")
        self.parser.add_argument("-T", "--timeout", help="the server timeout (in seconds) for the request")
        self.parser.add_argument("-s", "--silent", help="do not print any messages to standard output")

        group = self.parser.add_mutually_exclusive_group()
        group.add_argument("-a", "--abort", action='store_true', help="abort the import if there are any bad records")
        group.add_argument("-p", "--allow-partial-import", action='store_true', help="do not abort the import if there are any bad records")

        self.parser.add_argument("-k", "--key", help="the name of the encryption key to encrypt bad records in S3")

class ImportCredentialsCommand(ImportDelimCommand):
    name = 'import-credentials'
    desc = 'import a delimited file with credentials information'

    def add_commands(self):
        super(ImportCredentialsCommand, self).add_commands()

class CallCommand(WebClientCommand):
    name = 'call'
    desc = 'call a JSON service'

    def add_commands(self):
        super(CallCommand, self).add_commands()

        self.parser.add_argument("Service-URI", help='the service URI to connect to')
        self.parser.add_argument("-t", "--transport", help="transport configuration section")
        self.parser.add_argument("-n", "--no-compression", action='store_true', help='do not use GZIP compression on the wire')
        self.parser.add_argument("-i", "--input", metavar='FILE', help="input file or S3 URL")
        self.parser.add_argument("-o", "--output", metavar='FILE', help="output file or S3 URL")
        self.parser.add_argument("-f", "--format", action='store_true', help="format output nicely")
        self.parser.add_argument("-T", "--timeout", help="the server timeout (in seconds) for the request")
        self.parser.add_argument("-p", "--protobuf", action='store_true', help="the input is protobuf instead of JSON")
        self.parser.add_argument("-m", "--method", metavar='METHOD', help="the HTTP Method to use (POST/GET/DELETE).")
        self.parser.add_argument("--username", metavar='USERNAME', help="username to use in signature-based authentication.")
        self.parser.add_argument("--keyname", metavar='KEYNAME', help="private key name (alias) to use in signature-based authentication.")
        self.parser.add_argument("--keydir", metavar='KEYDIR', help="directory to search for keys in signature-based authentication. Defaults to keydir in lb-web-client.config.")


class IOCommand(WebClientCommand):
    def add_commands(self):
        super(IOCommand, self).add_commands()

        self.parser.add_argument('--input', '-i', help='input file')
        self.parser.add_argument('--output', '-o', help='ouptut file')

class BcryptCommand(IOCommand):
    name = 'bcrypt'
    desc = 'apply bcrypt hash to every line of a file, or standard input'


class HomeDirCommand(object):

    def __init__(self, subparsers, home):
        parser = subparsers.add_parser('home-dir', help="print the directory used for LB_WEBSERVER_HOME")
        def print_home(args):
            print home
        parser.set_defaults(func=print_home)

    def add_commands(self):
        pass
