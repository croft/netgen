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
import sys
import argparse
from argparse import RawTextHelpFormatter
import subprocess
import re
import copy
import itertools
from operator import itemgetter

g_args = []
g_messages = {}
g_plugins = []
g_makefile = None
g_default_prefix = None
g_deps = {}
g_compiledlibs = {}  # the compiled libraries found on the libpath
g_parsers = []
g_deps_locked = False
g_lb_version = None
g_projects = {}  # all lb_library Projects
g_workspaces = {}  # all Workspaces
g_rules = {}
g_variables = []
g_tasks = []

def to_file(file_name):
    """
    write the content of the IOString to a file
    """

    makefile = open(file_name, 'w')
    makefile.write(g_makefile.getvalue())
    makefile.close()


def reset():
    """
    this is used for testing lb-config
    """

    global  g_messages,g_plugins,g_makefile,g_default_prefix,g_deps,g_compiledlibs
    global  g_parsers,g_deps_locked,g_lb_version,g_projects,g_workspaces,g_rules,g_variables
    global g_tasks

    g_messages = {}
    g_plugins = []
    g_makefile = None
    g_default_prefix = None
    g_deps = {}
    g_compiledlibs = {}  # the compiled libraries found on the libpath
    g_parsers = []
    g_deps_locked = False
    g_lb_version = None
    g_projects = {}  # all lb_library Projects
    g_workspaces = {}  # all Workspaces
    g_rules = {}
    g_variables = []
    g_tasks = []


def emit(line, makefile=None):
    '''Add a line to the makefile'''
    write_to = makefile if makefile is not None else g_makefile
    write_to.write(line + '\n')


def variable(name, value):
    g_variables.append([name, value])


def rule(output, input, commands=None, phony=False, description=None):
    def rule_with_multiple_outputs(output, input, commands=None, makefile=None):
        prev_output = None
        for i, output in enumerate(output):
            if i == 0:
                rule(output, input, commands, description=description)
            else:
                rule(output, prev_output)
            prev_output = output

    if isinstance(input, basestring):
        input = input.split(' ')
    if type(output) == list and len(output) > 1:
        rule_with_multiple_outputs(output, input, commands)
    else:
        if type(output) is list:
            output = output[0]
        if type(input) is not list:
            input = [input]
        if commands is None:
            commands = []
        elif type(commands) is not list:
            commands = [commands]
        if output in g_rules:
            g_rules[output].input.update(input)
            g_rules[output].commands.extend(commands)
        else:
            g_rules[output] = Rule(output, input, commands, phony=phony, description=description)


## private
def write_variables():
    for name, value in g_variables:
        emit('%s = %s' % (name, value))


## private
def write_rules(makefile=None):
    ## write default rule (all) first
    def make_all_first(x, y):
        if x.output == 'all':
            return -1
        elif y.output == 'all':
            return 1
        else:
            return cmp(x.output, y.output)
    for rule in sorted(g_rules.itervalues(), cmp=make_all_first):
        rule.emit()


## private
class ConfigureError(Exception):
    pass


## private
def deprecation_alert(msg):
    print >> sys.stderr, "Deprecation warning: %s" % msg


## private
class Dependency:
    """A class which represents the dependencies of the configuration, i.e. the
    other build artifacts that are necessary in order to build the current
    project, e.g. LogicBlox. Each dependency will add a --with-<dep_name> option
    to the buildlb command line tool which will allow you to set the path
    of the dependency at configure time."""

    def __init__(self, name, path=None, default_path=None, optional=False, help=None):
        self.name = name
        self.path = os.path.expandvars(path) if path is not None else None
        self.default_path = os.path.expandvars(default_path) if default_path is not None else None
        if self.path is None and self.default_path is not None:
            self.path = self.default_path
        self.optional = optional
        self.help = help

    def is_optional(self):
        return self.optional

    def __str__(self):
        return str(vars(self))

    def __repr__(self):
        return self.__str__()

## private
def unlock_dependencies():
    """'Unocks' the set of dependencies such that you can now add
    dependencies. Do not use this method unless you know exactly what you
    are doing."""
    global g_deps_locked
    g_deps_locked = False


## private
def lock_dependencies():
    """'Locks' the set of dependencies such that you can no longer add
    dependencies. This was added to guard against modifications after initial
    setup which can cause weird issues."""
    global g_deps_locked
    g_deps_locked = True


## private
def get_dependencies():
    """Gets a dictionary of the current dependencies."""
    return copy.deepcopy(g_deps)


## private
def add_dependency(dependency):
    """Adds a dependency to the list of dependencies for this configuration.

    @param dependency: an instance of a Dependency object
    """
    global g_deps
    if g_deps_locked:
        raise ConfigureError("Dependency registered post-setup.  This is not allowed.")
    if dependency.name in g_deps:
        raise Exception('Dependency %s is declared multiple times. Dependencies configured in lbconfig_plugins.py should not be declared in config.py' % dependency.name)
    g_deps[dependency.name] = dependency


## private
def get_dependency_path(name):
    """Returns the current path for a dependency with the given name. Will throw
    an error if no path exists.

    @param name: the name of the dependency to look up
    """
    deps = get_dependencies()
    if name not in deps:
        raise ConfigureError("Unknown dependency: %s" % name)
    path = deps[name].path if deps[name].path is not None else deps[name].default_path
    if path is None:
        raise ConfigureError("No path found for dependency '%s'" % name)
    return path

def add_arg(args, kwargs):
    g_args.append([args, kwargs])

## private
def add_dependencies(dep_dict):
    """Given a dictionary of dependencies, it will create a Dependency object
    and add that object to the global list of dependencies.

    @param dep_dict: a dictionary representing the dependencies to add. The
                     keys should be the name of the dependencies and the values
                     should be a dictionary with one or more of the following
                     keys: default_path, help
    """
    for name, v in dep_dict.iteritems():
        add_dependency(Dependency(
            name,
            default_path=v.get('default_path'),
            path=v.get('default_path'),
            help=v.get('help'),
            optional=v.get('optional') in ("True", "true")))

def escape_for_bash_and_makefile(s):
    ## we use $$ to escape $ in makefile and \\$ to escape in bash
    return s.replace('"', '\\"').replace('$', '\\$$')

def escape_for_bash(s):
    ## we use $$ to escape $ in makefile and \\$ to escape in bash
    return s.replace('"', '\\"')

def format_with_arg(arg):
    return "--with-%s" % arg.replace('_', '-')

## private
def get_parser(default, plugins=None):

    deps = get_dependencies()
    for k, v in deps.iteritems():
        help = v.help + " " if v.help else ''
        if v.default_path is not None:
            help += "Defaults to %s." % v.default_path
        arg = format_with_arg(k)
        try:
            default.add_argument(arg , help=help, default=v.default_path, dest=k)
        except argparse.ArgumentError:
            raise Exception(
                'Dependency %s is already configured in lbconfig_plugins.json. Please remove from config.py' % k)

    for args, kwargs in g_args:
        default.add_argument(*args, **kwargs)

    return default


def add_plugin(module_name, build_dir, install_dir, deps):
    g_plugins.append({'module_name': module_name, 'build_dir': build_dir,
                      'install_dir': install_dir, 'deps': deps})


## private
def default_parser(subparsers):
    parser = subparsers.add_parser(
        'config',
        help='creates a Makefile for building LogicBlox projects',
        formatter_class=RawTextHelpFormatter,
        add_help=False)

    parser.add_argument('-h', '--help', action='store_true', help="show this help message and exit")
    parser.add_argument('-f', '--file', help='the configuration file to execute. Defaults to "config.py"', default="config.py")
    parser.add_argument('-e', '--extension',
        help='a python file that contains the lbconfig extensions. Will automatically load a file name "lbconfig_local.py"')
    global g_default_prefix
    default_prefix = g_default_prefix if g_default_prefix else 'out'
    parser.add_argument('-p', '--prefix', help='the installation prefix. In other words, where to put the output of "make install". Defaults to "out"',
        default=default_prefix)

    return parser

## private
def emit_dependencies():
    valid = True
    deps = get_dependencies()
    for k, v in deps.iteritems():
        if v.path is None:
            print "ERROR: Dependency %s has no specified path." % v.name
            valid = False

    if not valid:
        sys.exit(1)

    for k, v in deps.iteritems():
        emit("%s = %s" % (k, v.path))


## private
def set_default_prefix(prefix):
    global g_default_prefix
    g_default_prefix = prefix


def declare_parser_argument_variables(args):
    args = dict(args.__dict__.items())
    deps = get_dependencies()
    for k, v in args.iteritems():
        if k in deps:
            dep = deps.get(k)
            if dep is None:
                dep = deps.get(k.replace('_', '-'))
            if dep is None:
                raise ConfigureError("Unknown dependency: %s" % k)
            g_deps[k].path = v
        else:
            def to_str(v):
                if type(v) == bool:
                    return int(v)
                else:
                    return str(v)
            variable(k.replace('_', '-'), to_str(v))


## private
def setup(args):
    # Disable the silly default shell script rule
    declare_parser_argument_variables(args)

    rule('%', '%.sh')

    variable('lb', sys.argv[0])
    variable('V', '0')
    # Make variable trickery: If V=0 (the default), Q=Q0=@, so $(Q)cmd=@cmd in
    # a rule will run cmd without echoing it out. If V=1, Q=Q1= so $(Q)cmd=cmd
    # in a rule will run cmd after echoing it out.
    variable('Q0', '@')
    variable('Q1', '')
    variable('Q', '$(Q$(V))')

    variable('topdir', '$(shell pwd)')
    variable('build', '$(topdir)/build')

    variable('protoc', 'protoc')
    variable('proto2datalog', '$(logicblox)/bin/proto2datalog')

    variable('testcase', '')

    # only need to search compiled libraries if we have lb projects
    if g_projects:
        find_compiled_libraries()

    dist_target()
    check_target()
    install_target()


## private
def get_bloxweb_classpath():
    bloxweb_classpath = [
        '$(lb_web)/lib/java/lb-web-server.jar',
        '$(lb_web)/lib/java/lb-web-client.jar',
        '$(logicblox)/lib/java/lb-connectblox.jar']
    return bloxweb_classpath


# private
def get_current_lb_version():
    global g_lb_version
    if not g_lb_version:
        build_deps = get_dependencies()
        if not 'logicblox' in build_deps:
            raise Exception('Please set logicblox as a dependency.')
        # OPTMIZE_ME!
        # This check is slow. We can check 3.x vs 4.x by searching for
        # dlunit. Maybe there's a faster way to check 3.9 vs 3.10.
        ver = subprocess.Popen(
            ["%s/bin/lb" % build_deps['logicblox'].path, "version"],
            stdout=subprocess.PIPE).communicate()[0]
        if ver.startswith('Server is OFF'):
            ver = ''
        g_lb_version = ver.strip()

    return g_lb_version


## private
def find_compiled_libraries():
    global g_compiledlibs

    build_deps = get_dependencies()
    libPaths = []
    for key, value in build_deps.iteritems():
        if value.path.startswith("$("):
            env = os.getenv(value.path.replace("$(", "").replace(")", ""))
            if env is not None:
                libPaths.append(env)
            else:
                print "WARNING: Could not find environment variable %s. " \
                      "Some libraries may not build succesfully. " % \
                      value.path.replace("$(", "").replace(")", "")
        else:
            # If the dependency is the logicblox home, we add BlockResources to it
            # since that's the directory that contains library. This speeds up lb config
            # a lot.
            path = value.path + '/share/logicblox/BlockResources' if key == 'logicblox' else value.path
            abspath = os.path.abspath(path)
            if os.path.exists(abspath):
                libPaths.append(path)
            else:
                print "WARNING: Could not find value for arg %s. Path %s " \
                      "does not exist. Some libraries may not build succesfully. " \
                      % (key, abspath)

    libPath = ":".join(libPaths)

    # OPTMIZE_ME!
    # This code checks whether dependent libraries are installed. It does so by
    # calling bloxlibraries. We should check if there's some faster way to do
    # this because it is taking a lot of time to compute.
    if len(libPath) > 0 and 'logicblox' in build_deps:
        results = subprocess.Popen([
            "%s/bin/lb" % build_deps['logicblox'].path,
            "libraries",
            "--libpath",
            libPath
        ], stdout=subprocess.PIPE).communicate()[0]
        lib_tuples = re.findall("Library '([:\w]+)'\\n   located in (.*)\\n", results)

        for libname, path in lib_tuples:
            if ':' in path:
                colons_in_path = True
                while colons_in_path is True:
                    path, tip = os.path.split(path)
                    if path == '':
                        break  # no path to be found
                    if not ':' in path:
                        colons_in_path = False

            g_compiledlibs[libname] = path


## private
def _phony(target, makefile=None):
    """Declare a target to be a phony target, so that a file with that
    name will not prevent make from executing that rule.

    The target parameter can contain multiple targets as a single
    space-delimited string."""
    emit('.PHONY: ' + target, makefile=makefile)


## private
def touch(file_path):
    base_path = os.path.dirname(file_path)
    return 'mkdir -p %s && touch %s' % (base_path, file_path)


## private
def flatten(seq):
    """Flattens a nested list or tuple.

    Example:

        >>> list(flatten([[1, 2], [3, 4]]))
        [1, 2, 3, 4]
    """
    for v0 in seq:
        # Don't recurse again unless it's a collection
        if isinstance(v0, (list, tuple)):
            for v1 in flatten(v0):
                yield v1
        else:
            yield v0


## private
class Rule(object):
    def __init__(self, output, input, commands, phony=False, makefile=None, description=None):
        self.output = output
        self.input = set(input)
        self.commands = commands
        self.is_phony = phony
        self.makefile = makefile
        self.description = description

    def emit(self):
        commands = list(flatten(self.commands))
        if self.is_phony:
            _phony(self.output)
        cont = ' \\' if self.input else ''
        emit('%s :%s' % (self.output, cont), makefile=self.makefile)
        last_input = len(self.input) - 1
        for i, dep in enumerate(self.input):
            tab = '\t'
            if last_input != i:
                cont = ' \\'
            else:
                cont = ''
            emit(tab + dep + cont, makefile=self.makefile)
        if commands:
            emit('', makefile=self.makefile)
        if len(self.commands):
            if self.description is not None:
                emit('\t@echo %s >&2' % self.description)
                silent = '$(Q)'
            else:
                silent = ''
            for cmd in commands:
                emit('\t%s%s' % (silent, cmd), makefile=self.makefile)

        # Always add a blank line at the end for readability.
        emit('', makefile=self.makefile)


## private
def lb_library_deps(project_file_name):
    '''Find all direct library dependencies of a project'''
    deps = []
    project_file = open(project_file_name, 'r')
    for line in project_file.readlines():
        if line.startswith('//'):
            continue
        parts = [f.strip() for f in line.split(',')]
        if len(parts) == 2 and parts[1] == 'library':
            deps.append(parts[0])
    project_file.close()
    return deps


## private
def files_used(project_filename):
    '''Find all files used in the given project file'''
    files = logic_files_used(project_filename)

    project_file = open(project_filename, 'r')

    for line in project_file.readlines():
        if line.startswith('//'):
            continue
        parts = [f.strip() for f in line.split(',')]

        ## soon this will be deprecated when we don't use
        ## descriptors in project files anymore
        if (len(parts) == 3 and (parts[1].endswith('.descriptor'))):
            files.append(parts[1])

        if (len(parts) >= 2) and (parts[1] == 'proto'):
            files.extend(parts[0].split(' '))

    project_file.close()
    return files


## private
def logic_files_used(project_filename):
    '''Find all logic files used in the given project file'''
    files = []
    project_file = open(project_filename, 'r')
    project_dirname = os.path.dirname(project_filename)

    for line in project_file.readlines():
        if line.startswith('//'):
            continue
        parts = [f.strip() for f in line.split(',')]
        if (len(parts) == 2 and (parts[0].endswith('.logic'))):
            files.append(parts[0])
        if (len(parts) >= 2 and parts[1] == 'module'):
            module_dir = os.path.join(project_dirname, parts[0])
            module_files = find_files(module_dir, '.logic')
            rel_module_files = [os.path.relpath(f, start=project_dirname) for f in module_files]
            files.extend(rel_module_files)

    project_file.close()
    return files


## private
def lb_library_project_file(name):
    '''The project file for the library with the given name'''
    liney_name = name.replace(':', '_')
    return liney_name + '.project'


## private
def lb_library_summary_file(name):
    '''Summary output file for a library'''
    slashy_name = name.replace(':', '_')
    return slashy_name + '/LB_SUMMARY.lbp'


## private
def lb_library_outdir(name):
    rel_summary_file = lb_library_summary_file(name)
    summary_file = '$(build)/sepcomp/' + rel_summary_file
    return os.path.dirname(summary_file)


## private
def expect_lb_version(ver):
    '''Report an error if the currently running LB version is not as expected'''
    lb_ver = get_current_lb_version()
    if None == lb_ver:
        raise ConfigureError('Could not get LB version.  Are lb services running?')
    if not lb_ver.startswith(ver):
        raise ConfigureError("Configuration expects LB version '" + ver + "' but found '" + g_lb_version + "'")


## private
def matches_version(ver):
    lb_ver = get_current_lb_version()
    return (None != g_lb_version) and lb_ver.startswith(ver)


## private
def lb_library_dependency(name):
    summary_file = lb_library_summary_file(name)
    return '$(build)/sepcomp/' + summary_file


## private
def check_lb_workspace_target(name):
    """
    Returns the check workspace target for the given name
    """
    return 'check-%s' % lb_workspace_target(name)


## private
def lb_workspace_target(name):
    """
    Returns the workspace target for the given name
    """
    return 'ws-' + name.replace(':', '-').replace('/', '-')


## private
def get_ws_archive_names(ws_name):
    ws_dir = '$(build)/workspaces'
    ws_export = ws_dir + '/' + ws_name
    ws_archive = ws_export + '.tgz'
    return [ws_dir, ws_export, ws_archive]


## private
def find_files(dirname, extension):
    '''utility to find all files with the given extension (e.g. .java) in a directory.'''
    result = []
    for dirpath, dirnames, filenames in os.walk(dirname):
        for filename in filenames:
            f = os.path.join(dirpath, filename)
            if f.endswith(extension):
                result.append(f)
    return result


# don't really like parsing through the proto file to find the java_package
# option, but dislike more having to set it in the proto file and pass it
# in to the buildlib functions
def get_java_package_from_proto(proto_file):
    f = open(proto_file)
    try:
        for line in f:
            s = line.strip()
            if not s.startswith('option'):
                continue
            l = len('option')
            s = s[l:].strip()
            if not s.startswith('java_package'):
                continue
            start = s.find('"')
            end = s.find('"', start+1)
            return s[start+1:end]
        return None
    finally:
        f.close()


## private
def splitall(path):
    """
    A simple function that splits a path into all into an array of all of its
    parts, including the file. For example, the path /a/b/c/d.py would result
    in the array:
        ['a','b','c','d.py']

    @param path: the path to split
    @return:     an array of the path nodes
    """
    head, body = os.path.split(path)
    results = [body]
    if "/" != head:
        if "/" in head:
            results = splitall(head) + results
        else:
            results = [head] + results
    return results


## private
def protobuf_pkg_prefix(package):
    pkgdir = package.replace('.', '/')

    if package == '':
        pkgprefix = ''
    else:
        pkgprefix = pkgdir + '/'

    return pkgprefix


## private
def get_java_protobuf_build_dir(name):
    return '$(build)/java/protobuf/' + name.title().replace('_', '')


## private
def service_start_target(service_name):
    return "start-service-%s" % service_name


## private
def service_stop_target(service_name):
    return "stop-service-%s" % service_name


## private
def service_started_file(service_name):
    return "$(build)/%s-service.started" % service_name


## private
def fix_install_destdir(destdir):
    #destdir should automatically include prefix unless
    # 1) the destdir argument is an absolute path
    # 2) the destdir argument already inclues the prefix
    #These exceptions are to support backwards-compatibility

    if destdir is None:
        raise ConfigureError("destdir argument to must not be None")
    is_abspath = os.path.abspath(destdir) == destdir
    includes_prefix = (destdir.split(os.path.sep)[0] == '$(prefix)')
    if includes_prefix:
        deprecation_alert("The path '%s' that was passed as the destdir argument "
                          "includes the installation prefix.  This is deprecated "
                          "as the installation prefix will automatically prepended." % destdir)

    if not (is_abspath or includes_prefix):
        destdir = os.path.join('$(prefix)', destdir)

    return destdir


## private
def dist_target():
    rule(
        output='dist_dir',
        input=[],
        commands=[
            'rm -rf $(package_name)',
            'mkdir -p $(package_name)'],
        description='Creating dist dir')
    rule(
        output='dist',
        input=['dist_files'],
        commands=[
            'tar zcvf $(package_name).tar.gz $(package_name)',
            'rm -rf $(package_name)'],
        description='Creating dist tarball')
    rule(
        output='distcheck',
        input=['dist'],
        commands=[
            'rm -rf $(build)/distcheck',
            'rm -rf $(build)/$(prefix)',
            'mkdir -p $(build)/distcheck',
            'cd $(build)/distcheck && ' + \
                'tar zxf ../../$(package_name).tar.gz',
            'cd $(build)/distcheck/$(package_name) &&' + \
                'lb config --prefix=$(build)/$(prefix)',
            'cd $(build)/distcheck/$(package_name) && ' \
                '$(MAKE)',
            'cd $(build)/distcheck/$(package_name) && ' \
                '$(MAKE) install',
            ],
        description='Testing dist tarball')


## private
def check_target():

    # If an app configuration has not generated a 'check' target, create a
    # default target that has an implicit dependency on the default 'all'
    # target.  The assumption here is that the app config should have control
    # over the 'check' dependencies instead of forcing a dependency on 'all'.
    # We also want to include the 'check' target, that will basically do
    # nothing, for standard continuous integration tools to rely on.
    global g_rules
    if not 'check' in g_rules:
        rule(
            output='check',
            input=['all'],
            phony=True)


## private
def install_target():

    # If an app configuration has not generated aa 'install' target, create a
    # default target that has an implicit dependency on the default 'all'
    # target.  The assumption here is that the app config should have control
    # over the 'install' dependencies instead of forcing a dependency on 'all'.
    # We also want to include the 'install' target, that will basically do
    # nothing, for standard continuous integration tools to rely on.
    global g_rules
    if not 'install' in g_rules:
        rule(
            output='install',
            input=['all'],
            phony=True,
            description='Installing files')


## private
def write_workspaces():
    """A function that writes the Make rules for creating all check-lb-workspaces."""
    check_targets = []
    warnings = []
    errors = []
    for ws in g_workspaces.values():
        check_targets.append(check_lb_workspace_target(ws.name))
        ws.populate()
        errors += ws.errors
        warnings += ws.warnings
        ws.write()

    rule(
        output='check-lb-workspaces',
        input=check_targets)
    return (warnings, errors)

def run_tasks():
    warnings = []
    errors = []
    for t in g_tasks:
        (run_warnings, run_errors) = t.run()
        warnings += run_warnings
        errors += run_errors

    return (warnings, errors)

def emit_clean_dir(dirname):
    '''Remove a directory on clean.'''
    rule(
        output='clean',
        input=[],
        commands='rm -rf ' + dirname)


def find_used_variables():
    pattern = re.compile('(?:[^\$]|\b)\$\(([\w-]+)\)')

    def all_strings():
        for var, value in g_variables:
            yield var
            if isinstance(value, basestring):
                yield value
        for rule in g_rules.itervalues():
            for input in rule.input:
                yield input
            yield rule.output
            for command in rule.commands:
                yield command
    for s in all_strings():
        if s:
            for m in pattern.findall(s):
                yield m


def check_lbconfig_package_called():
    if not 'package_name' in map(itemgetter(0), g_variables):
        add_error_message('lbconfig_package is mandatory and was not declared. ')


def check_all_variables_declared():
    '''Check that all uses of $(some-var) have some-var defined.'''

    used_vars = find_used_variables()
    duplicate_vars = set()
    declared_vars = set(['MAKE', 'PATH', 'PWD', 'HOME'])
    for var in itertools.chain(map(itemgetter(0), g_variables), g_deps):
        if var in declared_vars:
            duplicate_vars.add(var)
        else:
            declared_vars.add(var)

    if duplicate_vars:
        add_warning_message(
            'variables %s have been declared more than once. Check if '
            'you haven\'t declared variables that other dependencies or '
            'plugins declare.' % ', '.join(
                "'%s'" % s for s in duplicate_vars))

    missing_vars = set(used_vars).difference(declared_vars).difference(['package_name'])
    if missing_vars:
        add_warning_message(
            'variables %s have not been declared.' % ', '.join(
                "'%s'" % s for s in missing_vars))


def add_warning_message(message):
    add_validation_message(message, type='WARN')


def add_error_message(message):
    add_validation_message(message, type='ERROR')


def add_validation_message(message, type='WARN'):
    g_messages.setdefault(type, []).append(message)


def validate_makefile():
    check_lbconfig_package_called()
    check_all_variables_declared()


def is_makefile_valid():
    return 'ERROR' not in g_messages


def print_validation_messages():
    for error_type, messages in g_messages.iteritems():
        for m in messages:
            print >> sys.stderr, '%s: %s' % (error_type, m)

def create_manifest(manifest, jar_name, classes_dir, classpath, deps):
    # see the jar() method's manifest parameter for definition of the manifest options
    manifest_file = '%s/Manifest.txt' % classes_dir
    manifest_cmds = ['mkdir -p ' + classes_dir]

    if manifest.get('manifest_file') is None:
        # clear out previous file
        manifest_cmds.append("cat /dev/null > %s" % manifest_file)

        cp_prefix = manifest.classpath_prefix if manifest.get('classpath_prefix') else ''
        if manifest.get('add_classpath'):
            manifest_classpath = [os.path.split(p)[1] for p in classpath] # gets filename only

            if cp_prefix != '':
                # adds prefix to all files in cp
                manifest_classpath = [os.path.join(cp_prefix, p) for p in manifest_classpath]

            # need to write the classpath this way to avoid a "line to long" error in the jar command
            if len(manifest_classpath) >= 1:
                manifest_cmds.append("echo 'Class-Path: %s' >> %s" % (manifest_classpath.pop(), manifest_file))
                for cp in manifest_classpath:
                    manifest_cmds.append("echo '  %s' >> %s" % (cp, manifest_file))

        if manifest.get('main_class'):
            manifest_cmds.append("echo 'Main-Class: %s' >> %s" % (manifest.get('main_class'), manifest_file))

        # manifest files need empty line at end
        manifest_cmds.append("echo ' ' >> %s" % manifest_file)

        rule(
            output=manifest_file,
            input=deps,
            commands=manifest_cmds,
            description='Generating Manifest for %s' % jar_name)
    else:
        manifest_cmds.append('cp %s %s' % (manifest.get('manifest_file'), manifest_file))
        rule(
            output=manifest_file,
            input=deps + [manifest.get('manifest_file')],
            commands=manifest_cmds,
            description='Copying Manifest for %s' % jar_name)
