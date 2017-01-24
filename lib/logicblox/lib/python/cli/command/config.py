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

import imp
import json
import os
import re
import sys

# TODO - verify if this is needed.
bindir = os.path.dirname(os.path.realpath(__file__))
prefix = os.path.dirname(bindir)
sys.path.insert(0, '%s/lib/python' % prefix)

from lbconfig import api
from lbconfig import core
import cli.lbparser


def add_commands(parser, subparsers):
    """
        Add the default parser as a sub-command. The config command will
        reparse the command line only if it is the selected command.
    """
    config_parser = core.default_parser(subparsers)
    config_parser.set_defaults(extra_func=execute_config)
    return config_parser


def create_default_parser():
    """
        Create a shallow lb parser that only has the default config command.

        Return the main lb parser and the config sub parser.
    """
    parser = cli.lbparser.LBArgumentParser(prog='lb')
    return parser, core.default_parser(parser.add_subparsers())


def execute_config(args, extra, command_line):
    """
        This is called when config is the selected command. The args parameter
        will contain the recognized arguments of the core.default_parser, and
        extra will contain the remaining parameters.
    """

    # search for make in the PATH
    if not cli.util.which('make'):
        print "ERROR: Cannot find make in the PATH"
        return 1

    parser, config_parser = create_default_parser()

    # check that specification file exists
    if not os.path.exists(args.file):
        print "ERROR: Cannot find file configure file: %s" % args.file
        parser.print_usage()
        return 1

    # load plugins file and parse the command line, getting new args
    plugins_config_file = 'lbconfig_plugins.json'
    plugins, args = load_plugins(config_parser, args, plugins_config_file, command_line)

    # need to add the directory of the configure script so we can find
    # any imports such as buildlib_local relative to that file
    sys.path.insert(0, os.path.dirname(args.file))

    # declare a helper function for locating plugin modules
    def get_module_name(e):
        try:
            return re.match('No module named (.+)', str(e)).group(1)
        except:
            return 'module_name'

    # try to load the file that contains the config specification
    try:
        imp.load_source('configure', args.file)
    except ImportError as e:
        module_name = get_module_name(e)
        print >> sys.stderr, '%s as imported in %s.' % (e, args.file)
        print >> sys.stderr, (
            'Please declare plugins in %s.\n'
            'Sample lbconfig_plugins.json: {"%s": "python_path"}. \n'
            'And use the --with-*-plugin option to specify a path different '
            'from the default\n') % (plugins_config_file, module_name)
        config_parser.print_usage()
        return 1
    except IOError:
        print >> sys.stderr, (
            'Could not load file config.py. '
            'Use the file parameter to specify a different configuration file.')
        config_parser.print_usage()
        return 1

    ## first load plugin dependencies, then load our dependencies.
    ## our dependencies will override plugin dependencies
    if plugins:
        dependencies = load_plugin_dependencies(plugins, args)
        core.add_dependencies(dependencies)

    # finally get a new parser with any added plugins (which were added 
    # in the core's global state)
    parser, config_parser = create_default_parser()
    core.get_parser(config_parser, plugins)
    args = parser.parse_args(command_line)

    # execute the general help option
    if hasattr(args, 'help') and args.help:
        config_parser.print_help()
        return 0

    # now write the makefile, potentially using extensions
    default_extension_file = "lbconfig_local.py"
    extension = args.extension
    if extension is None and os.path.exists(default_extension_file):
        extension = default_extension_file

    return write_makefile(args, extension)



def load_plugins(config_parser, args, plugins_config_file, command_line):
    """
        Load the plugins defined in the plugins_config_file. Then, extend the config_parser
        with options for the plugin, and reparse the command line. The config_parser
        will not be extensible after this call because parsing the command line sets some 
        internal state.

        Return a tuple (plugins, new_args) where plugins is the structure loaded from
        the plugins_config_file and new_args is the recognized arguments of the command line
        as parsed after extending the parser with the plugin options.
    """
    plugins = {}
    new_args = args
    if os.path.exists(plugins_config_file):
        plugins = json.load(open(plugins_config_file))
        core.add_dependencies(plugins)
        core.get_parser(config_parser, plugins)
        new_args = config_parser.parse_known_args(command_line)[0]

        for dep_name in plugins:
            # if dep_name in args.__dict__:
            directory = new_args.__dict__.get(dep_name, None)
            if directory is None:
                raise Exception(('Could not find default path for %s plugin in %s. ' +
                                 'Please set %s parameter to specify proper path.') % (dep_name, plugins_config_file, core.format_with_arg(dep_name)))
            directory = new_args.__dict__[dep_name] + '/lib/python'
            print ('loading plugin %s from %s... ' % (dep_name, directory))
            sys.path.insert(0, directory)
            ## we reload lbconfig so that other plugins using
            ## lbconfig base name can be found when changing
            ## __path__ in __init__.py
            import lbconfig
            reload(lbconfig)

    return plugins, new_args




def load_plugin_dependencies(plugins, args):
    """
        Load and return the dependencies declared by plugins?
    """
    def load_dependencies(filename, plugin):
        try:
            return json.load(open(filename))
        except IOError:
            # if the plugin does not have dependencies there's no file anyway
            #print 'WARNING: Could not find file for dependencies for %s plugin %s' % (plugin, filename)
            return {}
    dependencies = {}
    ## sort to avoid non-determinism
    for plugin in sorted(plugins):
        deps = load_dependencies(
            os.path.join(
                args.__dict__[plugin],
                'lib', 'python',
                '.%s_deps' % plugin), plugin)
        for k, v in deps.iteritems():
            dependencies[k] = v

    return dependencies


def write_makefile(args, extension_file=None):
    '''
        After all the argument parsing, now actually process the arguments
        and write the makefile.
    '''
    core.setup(args)
    core.lock_dependencies()
    extension_files = [args.file]
    if extension_file:
        extension_files.append(extension_file)
    core.validate_makefile()
    core.print_validation_messages()
    if core.is_makefile_valid():
        api.write_makefile(extension_files)
        return 0
    else:
        return 1

