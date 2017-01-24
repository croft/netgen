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
import os
from cli import util
from web import util as webutil


def run(args, command_line, web_client_home):
    daemon = False
    if '--daemon' in command_line:
        daemon = True
        command_line.remove('--daemon')

    deps = ['lb-web-client.jar']

    deps_paths = [web_client_home + '/lib/java/' + name for name in deps]

    classpath = ':'.join(deps_paths)

    subenv = os.environ.copy()

    # make sure that we are using the correct webclient home (we may use the server as fallback)
    subenv['LB_WEBCLIENT_HOME'] = web_client_home
    subenv['LB_DEPLOYMENT_HOME'] = util.get_lb_deployment_home()

    config_dirs = []
    if 'LB_WEBCLIENT_HOME' in os.environ:
       config_dirs.append(os.environ.get('LB_WEBCLIENT_HOME') + '/config')

    config_dirs.append(util.get_lb_deployment_home() + '/config')


    config = util.load_global_config('lb-web-client', directories=config_dirs)
    if args.config:
        config.read(args.config)

    jvm_args = webutil.get_jvm_args('LB_WEBCLIENT_JVM_ARGS', config, 'lb-web-client-dump')
    java_args = ['java', '-Dfile.encoding=UTF-8'] + jvm_args + ['-cp', classpath, 'com.logicblox.bloxweb.client.Main']
    java_args.extend(command_line)

    if daemon:
        os.setsid()

    os.execvpe('java', java_args, subenv)
