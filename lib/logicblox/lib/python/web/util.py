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
import time
from cli.configutil import get_lb_deployment_home

def get_jvm_args(env_var, config, dump_name):
    jvm_arg_string = os.environ.get(env_var)
    if jvm_arg_string is not None:
        return jvm_arg_string.split()
    else:
        jvm_args = []
        if config.has_option('global', 'jvm_args'):
            jvm_args = config.get('global', 'jvm_args').split()        

        ## create memory dump on out of memory error
        if config.has_option('global', 'jvm_dump_dir'):
            dump_dir = config.get('global', 'jvm_dump_dir')
            dump_dir = dump_dir.replace('$(LB_DEPLOYMENT_HOME)', get_lb_deployment_home())
            if dump_dir.strip():
                def secondsSinceEpoch():
                    return time.mktime(time.localtime())

                jvm_args.extend([
                    '-XX:OnOutOfMemoryError=jmap -dump:file=%s/%s-%d.hprof %%p; kill %%p' %
                    (dump_dir, dump_name, int(secondsSinceEpoch()))])

        return jvm_args
