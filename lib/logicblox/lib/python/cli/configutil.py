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

from cli import lb_exception


import ConfigParser
import StringIO
import errno, os, sys
from signal import *
import time

class GlobalConfigParser(ConfigParser.RawConfigParser):
    """
       A helper class for parsing configuration files that have no sections.
    """
    def _read(self, fp, fpname):
        file = fp.read()
        newfile = StringIO.StringIO("[global]\n" + file)
        return ConfigParser.RawConfigParser._read(self, newfile, fpname)






# Takes the name of the configuration file as an argument, say 'lb-compiler',
# and and optionally a list of directories, say ['/user/foo/config']
def load_default_config(config_name, additional_dirs=None):
    """
      Helper method for loading and parsing configuration files, with no sections,
      from standard locations, as well as optionally additional directories
      provided.
    """

    env = os.environ
    dirs = []
    if 'LOGICBLOX_HOME' in env:
      dirs.append(env.get('LOGICBLOX_HOME') + '/config')

    dirs.append(get_lb_deployment_home() + '/config')

    if additional_dirs != None:
      dirs.extend(additional_dirs)

    return load_global_config(config_name, dirs)


def load_global_config(config_name, directories=None):
    dirs = [] if directories is None else directories

    configs = []
    for dir in dirs:
      configs.append(dir + '/' + config_name + '.config')

    config = GlobalConfigParser()
    config.read(configs)
    return config


def get_lb_deployment_home():
    return os.environ.get('LB_DEPLOYMENT_HOME', os.path.expanduser(os.path.join('~', 'lb_deployment')))

def get_env(key, default):
    if key in os.environ:
        return os.environ.get(key)
    else:
        return default
