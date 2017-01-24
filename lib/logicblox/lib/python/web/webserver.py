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
import getpass
import urlparse
import subprocess
import signal
import errno

import lb.web.admin
import lb.web.batch
import lb.web.credentials
import lb.web.service

from cli import lb_exception
from cli import util

from web import util as webutil

lb_deps = [
      'lb-common.jar',
      'lb-connectblox.jar',
      'lb-common-protocol.jar',
      'lb-compiler-protocol.jar',
      'junit-4.8.2.jar',
      'slf4j-api-1.7.1.jar',
      'slf4j-log4j12-1.7.1.jar',
    ]

prefix_deps = [
      'lb-web-server.jar',
      'bloxweb-credentials.jar',
      'bloxweb-email.jar'
    ]

lbprefix = os.environ.get('LOGICBLOX_HOME')
prefix = os.environ.get('LB_WEBSERVER_HOME')

lb_deps_paths = [lbprefix + '/lib/java/' + name for name in lb_deps]
prefix_deps_paths = [prefix + '/lib/java/' + name for name in prefix_deps]

def cmd_start(args):
    util.check_lb_server_on()

    classpath = ':'.join(prefix_deps_paths + lb_deps_paths)

    subenv = os.environ.copy()
    subenv['LB_WEBSERVER_HOME'] = prefix

    config_dirs = [prefix + '/config', util.get_lb_deployment_home() + '/config']

    config = util.load_global_config('lb-web-server', directories=config_dirs)
    if args.config:
        config.read(args.config)

    java_args = ['java', '-Dfile.encoding=UTF-8', '-XX:StringTableSize=100003']

    if (os.environ.get('LB_PRODUCTION_ENVIRONMENT') is None):
        java_args.extend(['-ea'])

    # precedence for environmental variable over config file for jvm args
    java_args.extend(webutil.get_jvm_args('LB_WEBSERVER_JVM_ARGS', config, 'lb-web-server-dump'))
    java_args.extend(['-cp', classpath, 'com.logicblox.bloxweb.Main'])

    if args.config:
        java_args.append(args.config)

    java_args = [os.path.expandvars(arg) for arg in java_args]

    pid_filename = _get_pid_filename()
    timeout = config.getint('global', 'startup_timeout')

    try:
        pid = util.check_process_running(pid_filename)
        print 'lb-web-server already running as PID %s ...' % pid
        return 1

    except:
        util.mkdirs(get_log_dir())

        daemonize = args.daemonize is not None and args.daemonize == 'true'
        log_filename = _get_log_filename(daemonize, config)

        # create the process
        if log_filename is not None:
            # redirect stdout and stderror to a log file
            try:
                logfile = open(log_filename, 'w')
            except IOError as e:
                print 'lb web-server failed to start: cannot open log_file to write: %s' % e
                return 1
            else:
                with logfile:
                    proc = subprocess.Popen(java_args, env=subenv, stdout=logfile, stderr=logfile)
        else:
            proc = subprocess.Popen(java_args, env=subenv)

        # try to start it
        try:
            if util.wait_for(check_status, timeout, "info: waiting for service 'web-server' to start (%d seconds remaining)", proc):

                # if success, set up pid file and maybe communicate with the process
                util.setup_pid_file(pid_filename, proc.pid, proc)
                print 'lb web-server started with PID %s' % proc.pid

                if not daemonize:
                    util.communicate(proc, pid_filename)
                return 0
            else:
                print 'lb web-server timed out while starting'

        except Exception as e:
            print 'lb web-server failed to start: %s' % e
        return 1


def get_log_dir():
    LOG_DIR = os.path.join(util.get_lb_deployment_home(), 'logs', 'current')
    return LOG_DIR


def _get_log_filename(daemonize, config):
    '''
        Get the name of the file to write logs into, if any.

        If the log should be written to a file (because the config has a property for the filename or because the config
        has no property at all and the server is not in daemon mode) then a filename is returned. Otherwise, None.

        @param daemonize whether the server is starting as a daemon.
        @param config the config file map.
    '''
    if not config.has_option('global', 'log_file'):
        # if not explicitcly configured, depends on daemonize
        if daemonize:
            LOG_DIR = get_log_dir()
            return os.path.join(LOG_DIR, 'lb-web-server.log')
        else:
            return None
    log_file = config.get('global', 'log_file')
    if log_file.strip == '-':
        return None
    return log_file

def _get_pid_filename():
    LOG_DIR = get_log_dir()
    return os.path.join(LOG_DIR, 'lb-web-server.pid')


def cmd_stop(args):
    """
        Stop the web-server, if it is running.

        @return True if the web-server was not running or if it was successfuly stopped.
        That is, return True if the web-server is stopped at the end of this function.
    """
    pid_filename = _get_pid_filename()
    try:
        pid = util.check_process_running(pid_filename)
        os.kill(int(pid), signal.SIGTERM)

        # wait to ensure that the web server is off. That is needed for the restart command,
        # otherwise cmd_start may run before the server is stopped and we will get an error.
        try:
            if util.wait_for(util.check_pid_func(pid, False), 10, "info: waiting for service 'web-server' to stop (%d seconds remaining)"):

                util.cleanup_pid_file(pid_filename)
                print 'lb web-server stopped'
                return 0

        except:
            pass
        print 'lb web-server timed out while stopping'
        return 1

    except Exception as e:
        util.cleanup_pid_file(pid_filename)
        print 'lb web-server not running'
        return 0

def cmd_restart(args):
    if cmd_stop(args) == 0:
        cmd_start(args)

def cmd_list(args):
    if args.services:
        list_services(args)
    if args.handlers or args.handler:
        list_handlers(args)
    if args.endpoints:
        list_endpoints(args)

def list_services(args):
    def find_group_endpoints(endpoints):
        group_endpoints = {}
        for endpoint in endpoints.endpoint:
            for group in endpoint.group:
                group_endpoints.setdefault(group, set()).add(endpoint.id)
        return group_endpoints

    admin_client = lb.web.admin.Client()
    services = admin_client.list_services()
    endpoints = admin_client.list_endpoints()
    group_endpoints = find_group_endpoints(endpoints)
    if args.verbose:
        print services
    else:
        table = [['Prefix', 'HTTP Method', 'Workspace', 'Groups', 'Disabled Status', 'Realm', 'Endpoints']]

        sorted_services = sorted(services.config, key=lambda service: get_service_key(service, group_endpoints))

        for s in sorted_services:
            groups = ','.join(s.service.group)
            endpoints = get_endpoints(s, group_endpoints)
            realm = s.service.authenticator if s.service.HasField('authenticator') else ''
            http_method = s.service.http_method
            workspace = s.workspace if s.workspace != '' else 'no workspace'
            disabled_status = s.service.disabled_status if s.service.HasField('disabled_status') else 'enabled'
            row = [s.service.prefix, http_method, workspace, groups, disabled_status, realm, endpoints]
            table.append(row)
        print_table(table)

def get_endpoints(service, group_endpoints):
    return ','.join(e for g in service.service.group
                            for e in group_endpoints.get(g, []) )

def get_service_key(service, group_endpoints):
    """
        This method returns a string to be used as the sorting key.
        In the current implementation it returns a pipe separated concatenation of all the fields.
    """
    return '|'.join(str(x) for x in
                [service.service.prefix,
                service.service.http_method,
                service.workspace,
                ','.join(service.service.group),
                service.service.disabled_status,
                service.service.authenticator,
                get_endpoints(service, group_endpoints)])

def list_handlers(args):
    admin_client = lb.web.admin.Client()

    if args.handler:
      # single handler
      if args.verbose:
        # verbose with a single handler, get global config
        handlers = admin_client.list_handlers(get_global_config=True, id=args.handler)
      else:
        # single handler, get local config
        handlers = admin_client.list_handlers(get_local_config=True, id=args.handler)

      if not handlers.handler:
        print "Handler with id '%s' is not loaded" % args.handler
      else:
        print "Configuration for handler with id '%s':" % args.handler
        print
        table = [['Key', 'Value']]
        for h in handlers.handler:
          #sorted(services.config, key=lambda service: service.service.prefix)
          for config in sorted(h.config, key=lambda c: c.key):
            table.append([config.key, config.value])
        print_table(table)

    else:
      # multiple handlers
      if args.verbose:
        # verbose with multiple handlers, get local configs for each
        handlers = admin_client.list_handlers(get_local_config=True)
        print handlers
      else:
        # just list the handlers
        handlers = admin_client.list_handlers()
      table = [['Id', 'Implementation classname']]
      for h in handlers.handler:
          table.append([h.id, h.classname])
      print_table(table)



def list_endpoints(args):
    admin_client = lb.web.admin.Client()
    endpoints = admin_client.list_endpoints()
    if args.verbose:
        print endpoints

    table = [['Id', 'Type', 'Groups', 'Port', 'Requires Authentication']]
    for e in endpoints.endpoint:
        row = [e.id, e.type, '-', '-', '-']
        if (len(e.group) > 0):
            row[2] = ','.join(e.group)
        if (e.HasField('port')):
            row[3] = str(e.port)
        if (e.authenticated):
            row[4] = 'yes'
        table.append(row)
    print_table(table)


def cmd_load_services(args):
    try:
        admin_client = lb.web.admin.Client()
        workspaces = [args.workspace] if args.workspace else []
        admin_client.start_service(workspaces=workspaces)
    except lb.web.service.HttpError, e:
        print e.content().exception
        sys.exit(1)

def cmd_unload_services(args):
    try:
        admin_client = lb.web.admin.Client()
        workspaces = [args.workspace] if args.workspace else []
        admin_client.stop_service(workspaces=workspaces)
    except lb.web.service.HttpError, e:
        print e.content().exception
        sys.exit(1)


def cmd_enable_services(args):
    try:
        admin_client = lb.web.admin.Client()
        admin_client.enable_service(prefix=args.prefix, endpoint=args.endpoint, method=args.method)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)


def cmd_disable_services(args):
    try:
        admin_client = lb.web.admin.Client()
        admin_client.disable_service(prefix=args.prefix, endpoint=args.endpoint, status=args.status, method=args.method)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)


def cmd_load(args):
    admin_client = lb.web.admin.Client()
    if args.jar is not None:
        handlers, workspaces = admin_client.install_config_from_jar(jar=[args.jar])
    else:
        handlers, workspaces = admin_client.install_config(config=[args.config])
    for h in handlers:
        print 'loaded handler', h
    if handlers:
        print
        print 'Note: services must be reloaded to use new handler configurations.'
    for w in workspaces:
        print 'loaded static workspace', w


def cmd_status(args):
    try:
        check_status()
        print 'lb-web-server is running.'
    except IOError as e:
        if e.errno == errno.ECONNREFUSED:
            raise lb_exception.LBServerOff('lb-web-server: connection refused (most likely server is not running)')
        raise lb_exception.LBServerOff("lb-web-server: unexpected error '%s'" % e)
    except:
        raise lb_exception.LBServerOff("lb-web-server: unexpected error '%s'" % e)

def check_status():
    # if there is no exception, then it is running
    admin_client = lb.web.admin.Client()
    admin_client.status()

def cmd_log(args):
    admin_client = lb.web.admin.Client()
    for cat in args.category:
        if cat.startswith('no-'):
            admin_client.set_log(cat[len('no-'):], False)
        else:
            admin_client.set_log(cat, True)


def cmd_loglevel(args):
    admin_client = lb.web.admin.Client()
    admin_client.set_database_loglevel(args.loglevel)


def cmd_monitor(args):
    admin_client = lb.web.admin.Client()
    predicates = admin_client.set_workspace_monitor(args.predname, args.remove, args.workspace)
    message = 'globally' if args.workspace is None else "for workspace '%s'" % args.workspace
    if not predicates:
        print 'There are no predicates currently monitored %s.' % message
    else:
        print 'Predicates currently monitored %s:' % message
        for r in sorted(predicates):
            print '  %s' % r

def cmd_export_users(args):
    # use lb-web-client so that s3 urls are supported
    lb.web.batch.export_delim(args.url, args.file)


def cmd_import_users(args):
    # use lb-web-client so that s3 urls are supported
    lb.web.batch.import_delim(args.url, input=args.file, full=args.full)


def cmd_set_password(args):
    pwd = getpass.getpass("enter password for user '" + args.username + "': ")

    url = urlparse.urlparse(args.url)
    client = lb.web.credentials.Client(host=url.hostname, port=url.port, path=url.path)

    try:
        client.set_password(args.username, pwd, create=args.create)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)

def cmd_reset_password(args):
    url = urlparse.urlparse(args.url)
    client = lb.web.service.Client(host = url.hostname, port = url.port, path = url.path)
    req = client.dynamic_request()
    req.user_name = args.username
    response = client.dynamic_call(req)
    if response.HasField('error'):
        print 'error: ', response.error, ' (code: ', response.erro_code, ')'
        sys.exit(1)

def cmd_confirm_reset_password(args):
    url = urlparse.urlparse(args.url)
    client = lb.web.service.Client(host = url.hostname, port = url.port, path = url.path)

    try:
        pwd = getpass.getpass("enter password: ")
        req = client.dynamic_request()
        req.change_token = args.token
        req.new_password = pwd
        response = client.dynamic_call(req)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)

    if response.HasField('error'):
        print 'error: ', response.error, ' (code: ', response.erro_code, ')'
        sys.exit(1)

def cmd_set_public_key(args):
    if not os.path.exists(args.filename):
        print 'error: no such file: ', args.filename
        sys.exit(1)

    url = urlparse.urlparse(args.url)
    client = lb.web.credentials.Client(host=url.hostname, port=url.port, path=url.path)

    try:
        client.set_public_key(args.username, args.filename, create=args.create)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)


def cmd_set_user_active(args):
    url = urlparse.urlparse(args.url)
    client = lb.web.credentials.Client(host=url.hostname, port=url.port, path=url.path)

    try:
        client.set_active(args.username, args.active == 'true', create=args.create)
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)


def cmd_list_users(args):
    url = urlparse.urlparse(args.url)
    client = lb.web.credentials.Client(host=url.hostname, port=url.port, path=url.path)

    try:
        users = client.list_users()
    except:
        print 'error:', sys.exc_info()[1]
        sys.exit(1)

    for u in users:
        print u


def print_table(table, header=1):
    '''
    A helper function to print formatted tables to standard output.
      table - must be a 2 dimensional list; each entry in the table list is a row.
      header - the number of rows in the table that are headers
    '''
    widths = []
    # compute the needed width for each column based on the longest string
    for row in table:
        for i in range(len(row)):
            w = len(str(row[i]))
            # first row
            if len(widths) <= i:
                widths.append(w)
            # other rows
            elif widths[i] < w:
                widths[i] = w
    # pad
    for i in range(len(widths)):
        widths[i] += 2

    # print the table
    if (header != 0):
        print_hline(widths)
    header_count = 0
    for row in table:
        for i in range(len(row)):
            if header_count < header:
                print str(row[i]).center(widths[i]),
            else:
                # pad
                print (' ' + str(row[i])).ljust(widths[i]),
        print

        # print hline after the headers, if any
        header_count += 1
        if (header != 0 and header_count == header):
            print_hline(widths)


def print_hline(widths):
    for i in range(len(widths)):
        print "-" * widths[i],
    print
