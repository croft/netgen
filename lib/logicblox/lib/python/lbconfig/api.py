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
import subprocess
import os
import core
import sys
import json
import StringIO
import types
import re

logicblox_dep = (
    "logicblox", {'default_path': "$LOGICBLOX_HOME",
                  'help': "The LogicBlox installation to use for this build."})
lb_web_dep = (
    "lb_web", {'default_path': "$LB_WEBSERVER_HOME",
                'help': "The lb-web-server installation to use for this build."})

def lb_deployment_dir():
    d = os.environ.get('LB_DEPLOYMENT_HOME')
    if not d:
        d = os.path.expanduser('~/lb_deployment')
    return d

core.variable('LB_DEPLOYMENT_HOME', lb_deployment_dir())

def depends_on(*deps, **more_deps):
    def to_dict(s):
        if isinstance(s, basestring):
            return {'default_path': s}
        else:
            return s

    dependencies = {}
    for k, v in deps:
        dependencies[k] = to_dict(v)
    for k, v in more_deps.iteritems():
        dependencies[k] = to_dict(v)
    core.add_dependencies(dependencies)

def with_arg(*args, **kwargs):
    core.add_arg(args, kwargs)

def lbconfig_package(name, default_prefix='out', version='', default_targets=['lb-libraries']):
    """Sets the name of the package and the list of targets that should be
    run when calling 'make'. The name of the package is used when creating
    tar.gz files in the 'make dist' command.

    @param name
        The name of the package is used when creating
        tar.gz files in the 'make dist' command.

    @param default_targets
        A list of strings that are the targets that should
        be run when calling 'make'.

    """
    core.set_default_prefix(default_prefix)
    rule('all', default_targets)
    if version:
        variable('version', version)
        variable('package_basename', '%s' % name)
        variable('package_name', '%s-$(version)' % name)
    else:
        variable('package_basename', '%s' % name)
        variable('package_name', name)


def emit(line, makefile=None):
    '''Add a line to the makefile'''
    print 'emit is deprecated.'
    core.emit(line, makefile)


def variable(name, value):
    '''Declare a variable in Makefile.

    Declares a variable in file as 'name = value'.

    @param name
        Name of variable.
    @param value
        Value of variable.

    '''
    core.variable(name, value)


def rule(output, input, commands=None, phony=False, description=None):
    '''A rule specifying commands to be invoked to make output files.

    @param output
        A list of output files, or a string with one output
        file.

    @param input
        A list of input files, or a string with one input file.

    @param commmands
        A list of commands to invoke that should make the
        output files.

    @param phony should be set to True if the output is a phony one
                  and not really a file.

    @param description
        A descriptive string to output when building the
        target in place of the commands being echoed.
    '''
    core.rule(output, input, commands, phony, description)


def target(name, deps):
    """
    Adds a project-specific target with a set of dependencies to the Makefile.
    This is useful for grouping sets of build tasks together and for defining
    the default Makefile target.

    @param name
        Name of the Makefile target.

    @param deps
        List of Makefile targets that the new target depends on.
    """
    rule(name, deps, phony=True)


def add_task(task):
    """
    Add a build task.

    @param task
        An object with a run() method which will be called after all lb_libraries and workspaces have been processed. The run method returns a list of errors.
    """
    if not type(task.run) is types.MethodType:
        print "Task %s does not have a run() method"%task
        system.exit(1)
    core.g_tasks.append(task)

def check_lb_library(**kwargs):
    '''Compiles an lb library, but does not install it.

    This accepts the same parameters as lb_library.
    '''
    kwargs['install'] = False
    lb_library(**kwargs)


def lb_library(name, srcdir, srcgen=[], deps=None, install=True, generated=False,
    scalable=None, install_subdir='share/$(package_basename)', post_cmds=[]):
    """
    Creates a make task to compile an LogicBlox library.

    @param name
        Project name (e.g. foo:bar).

    @param srcdir
        Directory that contains the .project file.

    @param srcgen
        An optional list of source files that are generated by some
        other build task. These files serve only to inform the Makefile
        that if they change then we should rebuild. srcgen file paths
        should be relative to the srcdir.

    @param deps
        An optional map of library name to directory name for
        dependencies on external libraries. System libraries and other
        libraries that are built by this build file are not required
        to be listed here.

    @param install
        Whether or not this library should be included in the
        'make install' task.

    @param generated
        Whether or not this library is generated and therefore we
        should not attempt to determine it's dependencies during
        the configure step.

    @param install_subdir

    @param post_cmds
        Optional list of commands to execute after the library is built.

    """
    if scalable is not None:
        core.deprecation_alert("Argument 'scalable' to lb_library is no longer relevant and is ignored")

    if name in core.g_projects:
        raise core.ConfigureError("Library %s already declared." % name)
    project = Project(name, srcdir, srcgen, deps, install, generated, install_subdir, post_cmds)
    core.g_projects[name] = project


def check_lb_workspace(name, libraries=[], native_libs=[], archived=False, init_cmds=[], input=[], compress=True, create_cmd=None, keep=False):
    """Creates a workspace and installs libraries into the workspace.

    Creates a target that creates a workspace with the given name & installs
    the libraries with the given names into the workspace. The libraries
    must have targets created via the lb_library or check_lb_library function.

    The target created will be named check-ws-<name> where name is the name
    parameter.

    @param name
        The name of the workspace to create. NOTE: if you put any '/'
        characters in the name you will not be able to use the
        auto-complete on the command line for the target name. This is
        a restriction of Make.

    @param libraries
        A list of library names to install into the newly
        created workspace.

    @param native_libs
        A list of native libraries to install in the workspace.

    @param archived
        Boolean - archive and compress the workspace -creates $(build)/workspaces/<name>.tgz

    @param init_cmds
        An optional list of commands to be executed after the workspace is
        created and libraries are installed but before the workspace is
        exported.

    @param input
        An optional list of make targets that this workspace creation depends
        on (jars with service implementations, for example)

    @param compress
        An optional Boolean value, when set to True will compress the exported workspace

    @param create_cmd
        Optionally define the exact command used to create the workspace. If this is set, the native_libs
        option will be ignored.

    @param keep
        If archived is true, keep controls whether the original workspace should
        be kept (true) or deleted (false).
    """
    if name in core.g_workspaces:
        raise core.ConfigureError("Workspace %s already declared.")
    workspace = Workspace(name, libraries, native_libs, archived, init_cmds, input, compress, create_cmd, keep)
    core.g_workspaces[name] = workspace


def ws_archive(name, libraries=[], init_cmds=[], input=[], compress=True, keep=False):
    """Archives a workspace.

    Creates a target that creates a workspace with the given name & installs
    the libraries with the given names into the workspace. The libraries
    must have targets created via the lb_library or check_lb_library function.
    The workspace will be exported and archived into a tgz file in the build
    directory.

    The target created will be named archive-ws-<name> where name is the name
    parameter.

    @param name
        The name of the workspace to create. NOTE: if you put any '/'
        characters in the name you will not be able to use the
        auto-complete on the command line for the target name. This is
        a restriction of Make.

    @param libraries
        An array of library names to install into the newly
        created workspace.

    @param init_cmds
        An optional list of commands to be executed after the workspace is
        created and libraries are installed but before the workspace is
        exported.

    @param input
        An optional list of make targets that this workspace creation depends
        on (jars with service implementations, for example)

    @param compress
        An optional Boolean value, when set to true, will compress the exported
        workspace

    @param keep
        If archived is true, keep controls whether the original workspace should
        be kept (true) or deleted (false).
    """
    check_lb_workspace(name, libraries, archived=True, init_cmds=init_cmds, input=input, compress=compress, keep=keep)


def import_ws_archive(name, ws_prefix=''):
    """
    Generate a makefile target prefixed by 'install-test-' followed by the
    specified workspace name.  This target can be used to import a workspace
    as a managed LB workspace from a workspace archive.  The ws_archive()
    function should be used to create the workspace archive.

    @param name
        The name of the workspace to create and the root name of a
        workspace archive that is in the $(build)/workspaces/ directory.

    @param ws_prefix
        Optional parameter that if specified will be prepended to
        the specified workspace name to form the managed
        workspace name.
    """
    archive_names = core.get_ws_archive_names(name)
    ws_archive = archive_names[2]
    commands = [
        'mkdir -p $(build)/ws_tmp/' + name,
        'cd $(build)/ws_tmp/' + name,
        'tar xzf ' + ws_archive,
        'cd ..',
        '$(lb) import-workspace --overwrite ' + ws_prefix + name + ' ' + name,
        'rm -rf ' + name]

    install_test_ws = 'install-test-' + name
    rule(
        output=install_test_ws,
        input=ws_archive,
        commands='&&'.join(commands),
        phony=True,
        description='Testing installing workspace ' + name
    )

    rule(
        output='install-test',
        input=install_test_ws,
        phony=True
    )


def check_protobuf_protocol(**kwargs):
    '''Creates files for protobuf protocol, but does not install them.

    This accepts the same parameters as protobuf_protocol.'''
    kwargs['install'] = False
    protobuf_protocol(**kwargs)


def python_protobuf(
        name,
        srcdir,
        package='',
        proto_paths=None,
        install=True):
    """
    Create a build task that will generate python wrappers from a protobuf
    protocol file.

    @param name
        Root name of the protocol (name of the .proto file without the extension).
    @param package
        The optional package that will contain the generated code.
    @param srcdir
        The directory containing the source .proto file.
    @param proto_paths
        Optional list of directories containing required protobuf protocol files used by the named protocol.
    @param install
        If True, will install files into $(prefix).
    """
    protobuf_protocol(
        name=name, package=package, srcdir=srcdir,
        proto_paths=proto_paths, gen_datalog=False,
        gen_java=False, gen_python=True, install=install)


def java_protobuf(
        name,
        srcdir,
        java_package,
        package='',
        proto_paths=None,
        install=True,
        outer_class=None):
    """
    Create a build task that will generate Java classes from a protobuf
    protocol file.

    @param name
        Root name of the protocol (name of the .proto file without the extension).
    @param java_package
        The name of the Java package to use when generating Java files. This should
        match the "option java_package" specified in the .proto file.
    @param package
        The optional package that will contain the generated code.
    @param srcdir
        The directory containing the source .proto file.
    @param proto_paths
        Optional list of directories containing required protobuf protocol files used by the named protocol.
    @param install
        If True, will install files into $(prefix).
    """
    protobuf_protocol(
        name=name, package=package, srcdir=srcdir, proto_paths=proto_paths,
        gen_datalog=False, gen_java=True, gen_python=False, outer_class=outer_class,
        java_package=java_package, install=install)


def protobuf_protocol(
        name,
        srcdir,
        package='',
        java_package=None,
        lifetime='transaction',
        proto_path='',
        gen_datalog=True,
        gen_java=True,
        outer_class=None,
        gen_python=True,
        install=True,
        proto_paths=None):
    '''Creates file for the protobuf protocol from proto files.

    @param name
        Root name of the protocol (name of the .proto file without the extension).
    @param package
        The optional package that will contain the generated code.
    @param srcdir
        The directory containing the source .proto file.
    @param java_package
        The (optional) name of the Java package to use when generating Java files.
        If not specified, Java code is not generated.
    @param lifetime
        The lifetime of the transaction for the datalog predicates.
    @param proto_path
        Optional path for protobuf protocol files used by the named protocol.
        This is deprecated. Use the proto_paths parameter instead.
    @param gen_datalog
        If True, will generate datalog files.
    @param gen_java
        If True and java_package is specified, will generate Java files.
    @param outer_class
        The name of the java class that contains protobuf code. If None, will use the default.
    @param gen_python
        If True, will generate python files.
    @param install
        If True, will install files into $(prefix).
    @param proto_paths
        Optional list of directories containing required protobuf protocol files used by the named protocol.
        The current dir and $(logicblox)/lib/protobuf are already included.
    '''
    if proto_paths is None:
        proto_paths = []
    proto_paths.append('.')
    proto_paths.append('$(logicblox)/lib/protobuf')
    if (proto_path is not None) and (proto_path != ''):
        proto_paths.append(proto_path)

    if java_package is None:
        gen_java = False
    else:
        java_pkgdir = java_package.replace('.', '/')

    pkgdir = package.replace('.', '/')
    pkgprefix = core.protobuf_pkg_prefix(package)

    rel_proto_file = pkgprefix + name + '.proto'
    proto_file = srcdir + '/' + pkgprefix + name + '.proto'

    # Rule for descriptor file and _proto.logic file
    proto_path_opt = ''
    for p in proto_paths:
        proto_path_opt = proto_path_opt + ' --proto_path ' + p

    if gen_datalog:
        logic_file = srcdir + '/' + pkgprefix + name + '_proto.logic'
        rel_logic_file = pkgprefix + name + '_proto.logic'
        descriptor_file = srcdir + '/' + pkgprefix + name + '.descriptor'
        rel_descriptor_file = pkgprefix + name + '.descriptor'

        rule([descriptor_file, logic_file], proto_file,
             ['mkdir -p ' + os.path.dirname(logic_file),
              'cd ' + srcdir +
                    ' && LOGICBLOX_HOME=$(logicblox)  '
                    ' $(proto2datalog) ' +
                    rel_proto_file + ' ' +
                    rel_descriptor_file +
                    ' -file ' +
                    rel_logic_file +
                    ' -lifetime ' + lifetime + proto_path_opt],
             description='Compiling protobuf protocol %s to datalog' % proto_file)

        emit_clean_file(logic_file)
        emit_clean_file(descriptor_file)

    if gen_python:
        py_file = python_protobuf_file(name, package)
        python_module_dir = os.path.dirname(py_file)
        rule(
            output=[py_file, python_module_dir],
            input=proto_file,
            commands=[
                'mkdir -p %s' % python_module_dir,
                'touch %s/__init__.py' % python_module_dir,
                'cd %s && $(protoc) %s --python_out $(build)/python %s' % (srcdir, rel_proto_file, proto_path_opt)
            ],
            description='Compiling protobuf protocol %s to python' % proto_file)
        rule(
            output='python-libraries',
            input=python_module_dir
        )
        core.emit_clean_dir('$(build)/python/' + pkgdir)
        depfile = python_protobuf_file(name, package)
        rule(output='python_protobufs', input=depfile, phony=True)

    if gen_java:
        java_build_dir = core.get_java_protobuf_build_dir(name)
        java_file = java_protobuf_file(name, java_package, outer_class)

        rule(
            output=[java_file, java_build_dir],
            input=proto_file,
            commands=[
                'mkdir -p %s' % java_build_dir,
                'cd %s && $(protoc) %s --java_out %s %s' % (srcdir, rel_proto_file, java_build_dir, proto_path_opt)
            ],
            description='Compiling protobuf protocol %s to java' % proto_file)

        core.emit_clean_dir('$(build)/java/' + java_pkgdir)
        depfile = java_protobuf_file(name, java_package, outer_class)
        rule(output='java_protobufs', input=depfile, phony=True)

    if install:
        install_file(proto_file, 'lib/protobuf/' + pkgdir)

    dist_files([proto_file])


def python_protobuf_file(name, package):
    '''Given a protobuf protocol name and a package, will return the full path
    to the generated Python file.

    @param name
        Root name of the protocol (name of the .proto file without the extension).
    @param package
        The optional package that will contain the generated code.
    '''
    return '$(build)/python/%s_pb2.py' % (core.protobuf_pkg_prefix(package) + name)


def java_protobuf_file(name, java_package = None, outer_class = None):
    '''Given a protobuf protocol name and a package, will return the full path
    to the generated Java file.

    @param name
        Root name of the protocol (name of the .proto file without the extension).
    @param java_package
        The (optional) name of the Java package to use when generating Java files.
        If not specified, Java code is not generated.
    '''
    if java_package is None:
        return ''

    java_pkgdir = java_package.replace('.', '/')
    title_name = name.title().replace('_', '') if(outer_class is None) else outer_class
    return core.get_java_protobuf_build_dir(name) + '/%s/%s.java' % (java_pkgdir, title_name)


def check_jar(
        name,
        main,
        srcdir=None,
        srcdirs=[],
        classpath=[],
        scala=False,
        scala_files=None,
        java_files=None,
        srcgen=[],
        deps=[],
        javadoc=None,
        manual_targets=None,
        workspaces=[],
        jvm_args=[],
        java_version="1.8",
        javac='javac',
        javac_flags="",
        scalac='scalac',
        scalac_flags="",
        resources=[],
        services=[],
        container_target='check',
        findbugs=False):
    '''Creates JAR package with test cases and adds tests to check target.

    @param name
        Name of jarfile, minus extension.
    @param main
        Name of executable class (has main method) to call to check jar.
    @param srcdir
        The directory where the sources are located.
        Directory can also contain scala files.
    @param srcdirs
        As list of directories where the sources are located.
        Directories can also contain scala files.
    @param classpath
        A list of jar files used for the java and scala classpath.
    @param srcgen
        A list of generated src files to also copy into this library
    @param scala
        True if we want to compile scala code. If we find any
        scala files in scala_files or srcdir, this is set to True.
    @param scala_files
        A list of scala files to compile.
    @param java_files
        A list of java files to compile.
    @param deps
        A list of dependency names to be added to the classpath. These should
    @param javadoc
        A dictionary with the 'title' of the Javadoc. If not set, will not
        generate Javadoc.
    @param manual_targets
        A list of other executable classes for checking, like main.
    @param resources
        A dictionary mapping file resources to relative locations within the
        jar. For backwards compatability, this can just be a list, in which
        case the files are all copied to the root of the jar.
    @param services:
        A list of services that should be be started before running this jar
    @param workspaces
        A list of workspace names that need to checked before checking this jar.
    @param java_version
        The Java version to use for compilation.
    @param container_target
        The target that will contain all check targets
    @param javac
        Path to the java compiler. Defaults to "javac".
    @param scalac
        Path to the scala compiler. Defaults to "scalac".
    @param findbugs
        Whether to generate a target to execute findbugs on the build.
    '''
    if manual_targets is None:
        manual_targets = {}
    jar(name, srcdir, srcdirs, classpath, srcgen, javadoc,
        deps=deps, install=False, scala=scala, scala_files=scala_files, java_files=java_files, java_version=java_version, resources=resources,
        javac=javac, javac_flags=javac_flags, scalac=scalac, scalac_flags=scalac_flags, findbugs=findbugs)

    jar_file = '$(build)/jars/' + name + '.jar'

    local_deps = ['$(build)/jars/' + d + '.jar' for d in deps]
    classpath = classpath + local_deps

    inputs = [jar_file]

    for service_name in services:
        inputs.append(core.service_started_file(service_name))

    for ws in workspaces:
        inputs.append(core.check_lb_workspace_target(ws))

    # TODO - this call to make is a hack because check_jar does not support proper setup and teardown of services, like check_command.
    # We need to refactor check_jar to use check_command, or at least extract the setup/teardown code from check_command.
    commands = ['java %s -cp %s:%s %s $(testcase)' % (' '.join(jvm_args), ':'.join(classpath), jar_file, main)]
    for service_name in services:
        commands.append('make stop-service-' + service_name)

    rule(
        output='check-' + name,
        input=inputs,
        commands=commands,
        description='Testing %s class of jar %s' % (main, name))

    rule(
        output=container_target,
        input=['check-' + name])

    for key, target in manual_targets.iteritems():
        rule(
            output='run-' + key,
            input=inputs,
            commands=[
                'java %s -cp %s:%s %s' %
                (' '.join(jvm_args), ':'.join(classpath), jar_file, target)],
            description='Testing %s class of jar %s' % (target, name))

def service_jar(name, srcdir = None, srcdirs = None, classpath = None,
        srcgen = None, javadoc = None, resources = None, deps = None,
        install = True, java_files = None, java_version = "1.8",
        protocols = None, findbugs=False):

    """
    Compiles a jar containing a bloxweb service implementation.

    See the jar() function for details on all parameters except for protocols.

    @param protocols
        List of protobuf protocol files that will be used to generate Java classes compiled into the jar.
    """
    if srcdirs is None:
        srcdirs = []
    if srcgen is None:
        srcgen = []
    if classpath is None:
        classpath = []
    if protocols is None:
        protocols = []
    if resources is None:
        resources = {}
    if deps is None:
        deps = []

    # add all bloxweb jars automatically to classpath
    bloxweb_cp = core.get_bloxweb_classpath()
    for p in bloxweb_cp:
        classpath.append(p)

    # generate java files from protocols and include generated files in the jar
    for proto_file in protocols:
        proto_pkg = core.get_java_package_from_proto(proto_file)
        pieces = os.path.split(proto_file)
        proto_src = pieces[0]
        proto_name = os.path.splitext(pieces[1])[0]
        protobuf_protocol(name=proto_name, srcdir=proto_src,
            java_package=proto_pkg, gen_java=True, gen_python=False,
            gen_datalog=False, install=install)

        jname = proto_name.title() + '.java'
        jname = jname.replace('_', '')
        pkg_path = proto_pkg.replace('.', '/')
        srcgen.append(core.get_java_protobuf_build_dir(proto_name) + '/' + pkg_path + '/' + jname)

    jar(name=name, srcdir=srcdir, srcdirs=srcdirs, classpath=classpath,
        srcgen=srcgen, javadoc=javadoc, resources=resources, deps=deps,
        install=install, java_files=java_files, java_version=java_version, findbugs=findbugs)


def jar(name,
        srcdir=None,
        srcdirs=[],
        classpath=[],
        srcgen=[],
        javadoc=None,
        resources=[],
        deps=[],
        install=True,
        scala=False,
        scala_files=None,
        java_files=None,
        java_version="1.8",
        manifest=None,
        javac='javac',
        scalac='scalac',
        scalac_flags="",
        javac_flags="",
        sbt=False,
        findbugs=False):
    '''
    Build a jar by compiling Java files with javac, and optionally Scala files with scalac.

    @param name
        Name of jarfile, minus extension.
    @param srcdir
        The directory where the sources are located.
        Directory can also contain scala files.
    @param srcdirs
        As list of directories where the sources are located.
        Directories can also contain scala files.
    @param classpath
        A list of jar files used for the java and scala classpath.
    @param srcgen
        A list of generated src files to also copy into this library.
    @param javadoc
        A dictionary with the 'title' of the Javadoc. If not set, will not
        generate Javadoc.
    @param resources
        A dictionary mapping file resources to relative locations within the
        jar. For backwards compatability, this can just be a list, in which
        case the files are all copied to the root of the jar.
    @param deps
        A list of dependency names to be added to the classpath. These should
        be contained within the dependencies in buildlib_local.py.
    @param install
        True if the jar should be installed into $(prefix).
    @param scala
        True if we want to compile scala code. If we find any
        scala files in scala_files or srcdir, this is set to True.
    @param scala_files
        A list of scala files to compile.
    @param java_files
        A list of java files to compile.
    @param java_version
        The Java version to use for compilation.
    @param manifest
        A dictionary of options for creating the manifest:

           add_classpath=False   # Adds the classpath entries to the manifest
           classpath_prefix=None # Adds a dir prefix (e.g. lib/) to each entry in the class path
           main_class=None       # Specifies a Main-Class for the Manifest
           manifest_file=None    # Specifies a file to use as the Manifest, ignores other options
    @param javac
        Path to the java compiler. Defaults to "javac".
    @param scalac
        Path to the scala compiler. Defaults to "scalac".
    @param scalac_flags
        Extra flags to pass to scalac
    @param javac_flags
        Extra flags to pass to javac
    @param sbt
        Build using sbt
    @param findbugs
        Whether to generate a target to execute findbugs on the build.
    '''
    if srcdir is not None:
        srcdirs = [srcdir] + srcdirs

    if java_files is None:
        java_files = []
        for d in srcdirs:
            java_files.extend(core.find_files(d, '.java'))

    if scala_files is not None:
        scala = True
    else:
        scala_files = []
        if scala:
            for d in srcdirs:
                scala_files.extend(core.find_files(d, '.scala'))

    if isinstance(resources, list):
        resourceKeys = resources
        resources = {}
        for f in resourceKeys:
            resources[f] = os.path.basename(f)
    else:
        resourceKeys = resources.keys()

    dist_files(java_files)
    dist_files(scala_files)
    dist_files(resourceKeys)
    java_files.extend(srcgen)

    jar_file = '$(build)/jars/' + name + '.jar'
    classes_dir = '$(build)/jars/' + name + '.classes'

    local_deps = ['$(build)/jars/' + d + '.jar' for d in deps]
    classpath = classpath + local_deps

    commands = ['mkdir -p ' + classes_dir]

    if (not sbt):
        if scala:
            commands.append(
                '%s %s -d %s -classpath %s %s' %          # do we wind up compiling java files twice?
                (scalac, scalac_flags, classes_dir, ':'.join(classpath), ' '.join(java_files + scala_files)))

        if java_files:
            commands.append(
                '%s %s -d %s -source %s -target %s -cp %s %s' %
                (javac, javac_flags, classes_dir, java_version, java_version, ':'.join(classpath + [classes_dir]), ' '.join(java_files)))
    else:
        sbt_srcs = ','.join( ("file(\\\"%s\\\")" if (d[0:1] == "/" or d[0:1]=="$") else "baseDirectory.value / \\\"%s\\\"") % d
                             for d in (java_files + scala_files))
        sbt_jars = ','.join("file(\\\"%s\\\")" % d for d in classpath)
        scalac_flags_list = scalac_flags.split(" ")
        javac_flags_list = javac_flags.split(" ")
        scalac_flags_str = ",".join("\\\"%s\\\"" % f for f in scalac_flags_list if f[0:2] != "-D" )
        javac_flags_str = ",".join("\\\"%s\\\"" % f for f in javac_flags_list if f[0:2] != "-D" )
        java_opts = " ".join( [f for f in scalac_flags_list if f[0:2] == "-D"]
                              + [f for f in javac_flags_list if f[0:2] == "-D"])
        commands.append("echo \"unmanagedSources in Compile := List( %s )\" > build.sbt" % sbt_srcs)
        commands.append("echo >> build.sbt")
        commands.append("echo \"unmanagedJars in Compile := List (%s).map(Attributed.blank)\" >> build.sbt" % sbt_jars)
        commands.append("echo >> build.sbt")
        commands.append("echo \"target := file(\\\"$(build)\\\")\" >> build.sbt")
        commands.append("echo >> build.sbt")
        commands.append("echo \"classDirectory in Compile := file (\\\"%s\\\")\" >> build.sbt" % classes_dir)
        commands.append("echo >> build.sbt")
        commands.append("echo \"scalacOptions in Compile := List (%s)\" >> build.sbt" % scalac_flags_str)
        commands.append("echo >> build.sbt")
        commands.append("echo \"javacOptions in Compile := List (%s)\" >> build.sbt" % javac_flags_str)
        commands.append("JAVA_OPTS=\"%s\" sbt compile" % java_opts)

    for f in resources:
        commands.append('mkdir -p %s/%s' % (classes_dir, os.path.dirname(resources[f])))
        commands.append('cp -a %s %s/%s' % (f, classes_dir, resources[f]))

    manifest_deps = []
    if manifest is not None:
        manifest_file = '%s/Manifest.txt' % classes_dir
        manifest_deps = [manifest_file]
        core.create_manifest(manifest, name, classes_dir, classpath, java_files + scala_files + resourceKeys + local_deps + classpath)

        commands.append('(cd %s; jar cfm ../%s.jar Manifest.txt .)' % (classes_dir, name))
    else:
        commands.append('(cd %s; jar cf ../%s.jar .)' % (classes_dir, name))

    rule(
        output=jar_file,
        input=java_files + scala_files + resourceKeys + local_deps + classpath + manifest_deps,
        commands=commands,
        description='Compiling jar ' + name)

    emit_clean_file(jar_file)
    core.emit_clean_dir(classes_dir)

    rule(
        output='jars',
        input=jar_file,
        phony=True)

    rule(
        output='jar-' + name,
        input=jar_file,
        phony=True)

    if install:
        install_file(jar_file, 'lib/java')

    if javadoc is not None:
        javadoc_dir = '$(build)/javadoc/' + name
        rule(
            output=javadoc_dir,
            input=java_files,
            commands=[
                'javadoc -classpath %s:%s -windowtitle "%s" -doctitle "%s" -link "%s" -link "%s" -link "%s" -public -d %s %s' %
                (
                    ':'.join(classpath),
                    classes_dir,
                    javadoc['title'],
                    javadoc['title'],
                    'http://docs.oracle.com/javase/6/docs/api/',
                    'http://docs.guava-libraries.googlecode.com/git/javadoc/',
                    'http://docs.amazonwebservices.com/AWSJavaSDK/latest/javadoc/',
                    javadoc_dir,
                    ' '.join(java_files))
            ],
            description='Generating javadoc for ' + name)

        if install:
            install_dir(javadoc_dir, 'docs/api/' + name)

    if findbugs:
        findbugs_html = '$(build)/' + name + '-findbugs.html'
        rule(
            output='findbugs',
            input=findbugs_html,
            commands=[
                'fb analyze -sourcepath %s -auxclasspath %s -effort:max -exclude findbugs-exclude-filter.xml -html -output %s %s' %
                (':'.join(srcdirs), ':'.join(classpath), findbugs_html, jar_file)
            ],
            description='Generating findbugs report for ' + name)


def python_library(package_name, srcdir=None, srcgen=[], python_files=None):
    """
    Copies the given python library into the $(build)/lib/python directory
    when running 'make' and into the $(prefix)/lib/python directory when
    running 'make install'. If no srdir is specified, it assumes the srcdir
    is a folder with the same name as the package name in the root directory.

    Creates the make target 'python-libraries'.

    @param package_name
        The root package name.
    @param srcdir
        The src directory in which to find the root package.
        Defaults to the root directory.
    @param srcgen
        A list of generated src files to also copy into this library.
    @param python_files
        A list of python files to consider for the library. By default,
        this function will search for all .py files in the package.
    """
    pydir = package_name if srcdir is None else os.path.join(srcdir, package_name)
    prefix = '' if srcdir is None else srcdir

    collect_python_files = False
    if python_files is None:
        python_files = []
        collect_python_files = True

    ## make sure we copy __init__.py files even if not specified in python_files
    for dirpath, dirnames, filenames in os.walk(pydir):
        for filename in filenames:
            f = os.path.join(dirpath, filename)
            if collect_python_files:
                if f.endswith('.py'):
                    python_files.append(f)
            elif filename == '__init__.py' and f not in python_files:
                python_files.append(f)

    outdir = "$(build)"
    for f in python_files:
        outfile = os.path.join(outdir, f)
        rule(
            output=outfile,
            input=f,
            commands=[
                'mkdir -p %s' % outdir,
                'mkdir -p %s/`dirname %s`'%(outdir,f),
                'cp -f %s %s/`dirname %s`'%(f,outdir,f)],
            description='Copying python library %s to the build dir' % f)
        rule(
            output='python-libraries',
            input=outfile)
        # only install python files that are not tests
        if '/test/' not in f:
            install_file(outfile, 'lib/python/' + os.path.dirname(f[len(prefix):]))


    pygendir = os.path.join('$(build)', 'python', package_name)
    for f in srcgen:
        prefixdir = os.path.join('lib', 'python', package_name, os.path.dirname(f))
        install_file(os.path.join(pygendir, f), prefixdir)

    dist_files(python_files)
    core.emit_clean_dir('$(build)/' + pydir)


def lbconfig_plugin(package_name, srcdir, plugin_module, plugin_deps=[]):
    '''Declare a python module as an lbconfig_plugin.

    @param srcdir
        The src directory in which to find the root package.
    @param plugin_module
        The module name for the plugin, for example 'lbconfig.jacoco'.
    @param plugin_deps
        A list of dependency names that are required to run this plugin.
        This will save a .[plugin-name]-deps file with the dependencies
        so that a config.py script can load the dependencies for
        the plugins that it uses.'''
    python_library(package_name, srcdir)
    if plugin_deps:
        core.add_plugin(
            plugin_module,
            build_dir=os.path.join('$(build)', 'python'),
            install_dir='lib/python/',
            deps=plugin_deps)


def bin_program(name):
    '''Name of a script or executable to be installed in $(prefix)/bin.

    @param name
        Name of script or executable.
    '''
    install_file(name, 'bin')
    dist_files([name])



def check_lbunit_suite(name,suite, workspaces=[], libraries=[], env=None, container_target='check'):
    """
    Emits a phony target that runs a suite lb-unit tests. The target will be name check-lb-unit-<name>

    @param suite
        The folder containing the test suite
    @param name
        The name the suite will be identified by
    @param workspaces
        An optional list of workspace names that this program
        depends on. The workspace must also be specified by the
        check_lb_workspace function.
    @param libraries
        The names of any lb libraries this program depends on. The
        libraries must be built by the lb_library or check_lb_library
        function.
    @param env
        A map of environment variables to set before executing the test program.
    @param container-target
        The target this check will be included in. By default 'check'
    """
    command = "$(lb) unit --suite-dir %s"%suite
    check_command("check-lbunit-%s"%name,command, name, workspaces, libraries, [], env, container_target=container_target)

def check_lbunit_test(name,test, workspaces=[], libraries=[], env=None,container_target='check'):
    """
    Emits a phony target that runs a lb-unit test. The target will be name check-lb-unit-<name>

    @param test
        The file containing the test
    @param name
        The name the suite will be identified by
    @param workspaces
        An optional list of workspace names that this program
        depends on. The workspace must also be specified by the
        check_lb_workspace function.
    @param libraries
        The names of any lb libraries this program depends on. The
        libraries must be built by the lb_library or check_lb_library
        function.
    @param env
        A map of environment variables to set before executing the test program.
    @param container-target
        The target this check will be included in. By default 'check'
    """
    command = "$(lb) unit --test %s"%test
    check_command("check-lbunit-%s"%name,command, name, workspaces, libraries, [], env, container_target=container_target)

def check_program(filepath, workspaces=[], libraries=[], name=None, services=[], env=None, container_target='check', input=None, params=''):
    """
    Emits a phony target that runs the file at the given file path. By default,
    the name of the target will be 'check-<folder>' where <folder> is the name
    of the immediate parent folder of the program to run. You can optionally
    use the name parameter to change the target to 'check-<name>'.

    @param filepath
        The file to run, relative to the root project directory.
    @param workspaces
        An optional list of workspace names that this program
        depends on. The workspace must also be specified by the
        check_lb_workspace function.
    @param libraries
        The names of any lb libraries this program depends on. The
        libraries must be built by the lb_library or check_lb_library
        function.
    @param name
        An optional parameter to change the name of the check target.
    @param services
        A list of services this test depends on.
    @param env
        A map of environment variables to set before executing the test program.
    @param container-target
        The target this check will be included in. By default 'check'
    @param input
        An optional list of make target names that are required before running the check program.
    @param params
        An optional string to be appended to the file to run. Usually includes hardcoded parameters to the executable.
    """
    if name is None:
        paths = core.splitall(filepath)
        assert len(paths) >= 2, "The test file for check_program must be in a folder(s). Paths: %s File: %s" % (paths, filepath)
        suite_name = paths[-2]
    else:
        suite_name = name

    check_target = 'check-%s' % suite_name

    all_deps = [filepath]
    if input is not None:
        for d in input:
            all_deps.append(d)

    ## add makefile variable that can be used to
    ## select the testcase we want to run
    command = '%s %s $(testcase)' % (filepath, params)

    result_file = check_command(check_target, command, suite_name, workspaces, libraries, services, env, extra_inputs=all_deps, container_target= container_target)
    dist_files([filepath])
    return {'check_target': check_target, 'result_file': result_file}



def check_command(check_target,command,suite_name, workspaces=[], libraries=[], services=[], env=None, extra_inputs=[], container_target='check'):
    """
    Low level entry point to check a command, used by check_program and check_lbunit


    @param check-target
        The name of the target
    @param command
        The command which will be run
    @param suite_name
        The name of the test.
    @param workspaces
        An optional list of workspace names that this program
        depends on. The workspace must also be specified by the
        check_lb_workspace function.
    @param libraries
        The names of any lb libraries this program depends on. The
        libraries must be built by the lb_library or check_lb_library
        function.
    @param services
        A list of services this test depends on.
    @param env
        A map of environment variables to set before executing the test program.
    @param extra_inputs
        A list of targets this depends on
    @param container-target
        The target this check will be included in. By default 'check'
    """


    # test setup
    setup_file = os.path.join("$(build)", "%s.setup" % check_target)
    setup_commands = [
        'mkdir -p $(build)'
    ]
    setup_inputs = []
    for service_name in services:
        setup_inputs.append(core.service_started_file(service_name))
    for ws in workspaces:
        setup_inputs.append(core.check_lb_workspace_target(ws))
    for lib in libraries:
        rel_summary_file = core.lb_library_summary_file(lib)
        summary_file = '$(build)/sepcomp/' + rel_summary_file
        setup_inputs.append(summary_file)

    rule(
        output=setup_file,
        input=setup_inputs,
        commands=setup_commands,
        description='Setting up for test suite ' + suite_name
    )

    # compute the string to export environment variables

    env_string = ''
    if env is not None:
        env_string = " ".join("%s=%s" % (key, value) for key, value in env.items())

    # test execution
    # writes status code to result file which will then be checked in the
    # main 'check' command. This allows all tests to run and therefore capture
    # all errors before failing.
    result_file = os.path.join("$(build)", "%s.result" % check_target)
    result_commands = [
        '%s %s ; echo $$? > %s' % (env_string, command, result_file)
    ]
    result_inputs = [ setup_file ]
    for i in extra_inputs:
        result_inputs.append(i)
    rule(
        output=result_file,
        input=result_inputs,
        commands=result_commands,
        description='Running test command ' + command
    )
    emit_clean_file(setup_file)
    emit_clean_file(result_file)


    # test teardown
    teardown_target = "teardown-%s" % suite_name
    teardown_inputs = [result_file]
    for service_name in services:
        teardown_inputs.append(core.service_started_file(service_name))
        teardown_inputs.append(core.service_stop_target(service_name))
        rule(
            output=core.service_stop_target(service_name),
            input=result_file
        )

    teardown_commands = ['rm -f %s' % setup_file]
    rule(
        output=teardown_target,
        input=teardown_inputs,
        commands=teardown_commands,
        phony=True,
        description='Tearing down test suite ' + suite_name
    )

    # check target
    # fails if the result file has a bad error code
    rule(
        output=check_target,
        input=[result_file, teardown_target],
        commands=['$(Q)test $$(cat %s) = "0"' % result_file],
        phony=True
    )

    rule(
        output=container_target,
        input=check_target
    )
    return result_file



def config_file(name):
    '''A configuration file that should be installed into $(prefix)/config'''
    install_file(name, 'config')
    dist_files([name])


def install_files(filenames, destdir):
    '''Install a list of files into $(prefix)/destdir.

    @param filenames
        A list of files to copy.
    @param destdir
        Target directory to copy to.
        This should be a relative directory name.'''
    for f in filenames:
        install_file(f, destdir)


def install_file(filename, destdir):
    '''Install a file into $(prefix)/destdir.

    @param filename
        Source file to copy.
    @param destdir
        Target directory to copy to.
        This should be a relative directory name.'''
    destdir = core.fix_install_destdir(destdir)
    rule(
        output='install',
        input=filename,
        commands='mkdir -p ' + destdir + ' && cp -pf ' + filename + ' ' + destdir,
        description='Installing files into $(prefix)')


def install_dir(dirname, destdir, allow_empty=False):
    '''Install contents of a directory into $(prefix)/destdir.

    @param dirname
        Source directory to copy from (relative to the directory running make)
    @param destdir
        Target directory to copy to.
        This should be a directory name relative to the install directory.
    @param allow_empty
        If true, allow that the source directory be empty, so the destdir will
        still be created but without contents. If false, it is an error when the
        source directory is empty.
    '''
    destdir = core.fix_install_destdir(destdir)
    copy_command = 'cp -fR %s/* %s || echo "Skipping installation of empty directory \'%s\'" ' % (dirname, destdir, dirname)
    if allow_empty:
      copy_command = 'ls %s/* &>/dev/null && %s' % (dirname, copy_command)
    rule(
        output='install',
        input=dirname,
        commands='mkdir -p %s && %s ' % (destdir, copy_command),
        description='Installing files into $(prefix)')


def dist_files(files):
    '''Make a list of files part of the source distribution'''
    copy_commands = []
    for f in files:
        copy_commands.append('mkdir -p $(package_name)/`dirname %s`'%f)
        copy_commands.append('cp -f %s $(package_name)/`dirname %s`'%(f, f))

    rule(
        output='dist_files',
        input='dist_dir',
        commands=copy_commands,
        description='Copying files to dist dir')

    rule(
        output='dist_dir',
        input=files)


def dist_dir(directory):
    '''Make a directory recursively part of a distribution'''
    files = []
    for dirpath, dirnames, filenames in os.walk(directory):
        for filename in filenames:
            f = os.path.join(dirpath, filename)
            files.append(f)
    dist_files(files)


def copy_file(src, target):
    '''A rule to copy a file.

    @param src
        File to copy.
    @param target
        Destination.'''
    rule(
        output=target,
        input=src,
        commands='cp -f $< $@',
        description='Copying %s to %s' % (src, target))


def emit_clean_workspace(workspace, success_file="."):
    '''Remove a workspace on clean.

    @param workspace
        Workspace name.
    @param success_file
        Success_file that was created when the workspace
        was created. We only delete the workspace if this file
        exists. Defaults to . so that we always delete by default.'''
    rule(
        output='clean-workspaces',
        input=[],
        # the minus makes it not stop if it fails
        # use if condition to only delete existing workspaces
        # this speeds up clean operation significantly
        commands="-if [ -e %s ]; then lb delete --force %s;fi" % (success_file, workspace),
        description='Cleaning up')
    emit_clean_file(success_file, 'clean-workspaces')
    rule('clean', input=['clean-workspaces'])


def emit_clean_file(filename, output='clean'):
    '''Remove file on clean.'''
    rule(
        output=output,
        input=[],
        commands='rm -f ' + filename,
        description='Cleaning up')


def link_libs(libraries):
    '''
        Create a 'link_libs' phony target that, when called, will create a lib/ directory in the source
        folder, and then will create symlinks from this lib/ directory to the libraries passed as parameter.
        This is useful to set up IDEs that need references to all dependencies.
    '''
    link_commands = ['mkdir -p lib']
    for dep in libraries:
      link_commands.append('ln -f -s ' + dep + ' lib/')

    rule(
      output='link_libs',
      input=[],
      phony=True,
      commands=link_commands,
      description='Setting up links for library dependencies.'
    )

    rule(
        output='clean',
        input=[],
        commands='rm -f lib/*',
        description='Cleaning up library links')


### THESE ARE PRIVATE FUNCTIONS THAT END USERS SHOULD NOT USE
### They are here because they depend on the public api.
### As we improve lbconfig, we should move these private methods to core.py

## private
def write_lbconfig_deps(build_dir, module_name, deps, install_dir):
    def make_dict(dep):
        return {'default_path': '$(%s)' % dep.name, 'help': dep.help}
    dependencies = dict((k,make_dict(dep)) for k,dep in core.get_dependencies().iteritems())
    dep_file = '%s/.%s_deps' % (build_dir, module_name)
    deps = dict((dep, dependencies[dep]) for dep in deps)
    rule(dep_file, [],
         ['$(Q)mkdir -p %s' % os.path.split(dep_file)[0],
          '$(Q)echo %s > %s' % (core.escape_for_bash(json.dumps(deps)), dep_file)],
         phony=True)
    emit_clean_file(dep_file)
    install_file(dep_file, install_dir)


## private
def write_projects():
    """A function that writes the Make rules for all LB projects."""
    install_libraries = []
    check_libraries = []
    all_dist_files = []
    warnings = []
    errors = []
    for p in core.g_projects.values():
        # first do all the I/O & dependency analysis
        p.populate()
        errors += p.errors
        warnings += p.warnings

    for p in core.g_projects.values():
        p.write()

        all_dist_files.extend(p.real_src_dependencies())

        if p.install:
            install_libraries.append(p.summary_file)
        else:
            check_libraries.append(p.summary_file)

    rule(
        output='lb-libraries',
        input=install_libraries)

    rule(
        output='check-lb-libraries',
        input=check_libraries)

    dist_files(all_dist_files)
    return (warnings, errors)

## private
def write_makefile(extension_files=[],makefile_name='Makefile'):
    '''Close the makefile'''
    core.g_makefile = StringIO.StringIO()
    warnings = []
    errors = []
    core.emit_dependencies()

    # get projects' errors and warnings
    (proj_warnings, proj_errors) = write_projects()
    warnings += proj_warnings
    errors += proj_errors

    # get workspaces' errors and warnings
    (ws_warnings, ws_errors) = core.write_workspaces()
    warnings += ws_warnings
    errors += ws_errors

    # get tasks' errors and warnings
    (task_warnings, task_errors) = core.run_tasks()
    warnings += task_warnings
    errors += task_errors

    # OPTMIZE_ME!
    # The following code checks whether the dependency directories/files actually
    # exist. It does so by generating a temporary makefile and calling it repeatedly.
    # This is very inefficient, so it takes a long time. We could check it directly
    # in python.
    deps = core.get_dependencies()
    for k, v in deps.iteritems():
        dep = k
        if v.path.startswith('$') and not v.path.startswith('$('):
            # is an environment variable, must test differently
            command = '$(Q)test %s && test -e %s' % (v.path, v.path)
        else:
            command = '$(Q)test -e $(%s)' % dep
        rule('check-argument-' + dep, [], command)

    for plugin in core.g_plugins:
        write_lbconfig_deps(
            plugin['build_dir'], plugin['module_name'], plugin['deps'], plugin['install_dir'])

    if extension_files:
        dist_files(extension_files)

    core.write_variables()
    core.write_rules()
    # writing to a tmp file to check variable using make check-argument-
    tmp_file = "%s_tmp"%makefile_name
    core.to_file(tmp_file)
    for k, v in deps.iteritems():
        dep = k

        check = subprocess.call(['make', '-f', tmp_file, 'check-argument-' + dep],
                                stdout=open(os.devnull, "w"),
                                stderr=subprocess.STDOUT)
        if check != 0:
            if deps[dep].is_optional():
                print 'warning: directory \'{0}\' for \'{1}\' does not exist'.format(v.path, dep)
            else:
                print 'error: directory \'{0}\' for \'{1}\' does not exist'.format(v.path, dep)
                sys.exit(1)
    # report errors and exit
    if len(errors) > 0:
        for er in errors:
            print "ERROR:%s\n"%er
            sys.exit(1)
    # report warnings
    if len(warnings) > 0:
        for w in warnings:
            print "WARN:%s\n"%w
    os.remove(tmp_file)
    core.to_file(makefile_name)


## private
class Project(object):
    """Represents an LB project file and it's dependencies. The object is
    responsible for writing out the Make rules for an LB project."""

    def __init__(self, name, srcdir, srcgen=[], deps=None, install=True,
      generated=False, install_subdir='share/$(package_basename)',
      post_cmds=[]):
        # the library name
        self.name = name
        # the root directory for the source files
        self.srcdir = srcdir
        # any src files that are generated and therefore not available at
        # configure time
        self.srcgen = srcgen
        # any libraries this project depends on that the user explicitly listed
        if not deps:
            self.deps = {}
        elif type(deps) is list:
            self.deps = dict((dep, '$(%s)' % dep) for dep in deps)
        else:
            self.deps = deps
        # whether or not this project should be installed in the 'make install'
        # target
        self.install = install
        self.install_subdir = install_subdir
        # whether or not this project is generated
        self.generated = generated
        # optional commands to execute after the project is built
        self.post_cmds = post_cmds

        sepcomp = '$(build)/sepcomp'
        slashy_name = self.name.replace(':', '_')

        # the project file path for this project
        self.project_file = "%s/%s.project" % (self.srcdir, slashy_name)
        if not generated and not os.path.exists(self.project_file):
            raise core.ConfigureError("Could not find %s/%s.project for library %s." % (self.srcdir, slashy_name, name))

        # the resulting summary file path for this project
        self.summary_file = "%s/%s/LB_SUMMARY.lbp" % (sepcomp, slashy_name)
        # the directory where the seperately compiled project will be placed
        self.outdir = os.path.dirname(self.summary_file)

        # The following are populated in the populate() method which should
        # be called after object construction

        # any libraries this project depends on that are not compiled by
        # buildlib. These are typically system libraries like bloxweb.
        self.compiled_libraries = {}
        # the names of all dependent libraries, source & compiled
        self.dependent_libraries = []
        # a list of all source files for this project
        self.source_dependencies = []
        # a list of all file dependencies from other libraries, typically they
        # are lb summary files
        self.library_dependencies = []

        self.related_projects = {}
        self.warnings= []
        self.errors=[]


    def populate(self):
        """Populate is responsible for doing all the I/O dirty work such as
        parsing the project file to determine source files & project
        depenencies. We don't do this in the constructor so that you can set
        these values independently in tests."""

        if not self.generated:
            # lb_library_deps will want to parse the associated .project file,
            # only safe for projects that are not being generated at configure/build time
            self.dependent_libraries = core.lb_library_deps(self.project_file)

        self.dependent_libraries.extend(self.deps.keys())

        for dep in self.dependent_libraries:
            found_dep = False
            if dep in self.deps:
                found_dep = True
                self.compiled_libraries[dep] = self.deps[dep]
                # if a dep is explicitly specified in the deps, then
                # don't continue to consider other ways of finding it.
                continue
            if dep in core.g_compiledlibs:
                found_dep = True
                self.compiled_libraries[dep] = core.g_compiledlibs[dep]
            if dep in core.g_projects:
                found_dep = True
                self.related_projects[dep] = core.g_projects[dep]
            if not found_dep:
                self.errors.append("Library %s, needed by %s, not found."%(dep, self.name))
        self.source_dependencies = self._get_source_dependencies()
        self.library_dependencies = self._get_library_dependencies(self.dependent_libraries)

    @property
    def libpath(self):
        """A helper function for determining the libpath for this project.
        Should only be called after populate() has been called."""

        libpath = ['$(build)/sepcomp']
        for dep in self.compiled_libraries.values():
            libpath.append(dep)
        for p in self.related_projects.values():
            libpath.extend(p.libpath.split(":"))

        return ":".join(frozenset(libpath))

    def _get_library_dependencies(self, dependent_libraries):
        dependencies = []
        for dep in dependent_libraries:
            if  dep in core.g_projects:
                dependencies.append(core.g_projects.get(dep).summary_file)

        return dependencies

    def _get_source_dependencies(self):
        """A helper function for determining all the source file depenencies
        for this project."""

        project_file_dir = os.path.dirname(self.project_file)
        dependencies = []
        if not self.generated:
            files = core.files_used(self.project_file)
            dependencies = [self.project_file]
            for dep in files:
                dependencies.append(os.path.join(project_file_dir, dep))

        # generated source files in modules might not have been found yet
        # (they don't exist at configure time), so we extend the
        # dependencies.
        dependencies.extend([os.path.join(project_file_dir, src) for src in self.srcgen])

        return dependencies

    def real_src_dependencies(self):
        """Collect the files to distribute, removing the generated source files."""

        real_src_files = []
        if not self.generated:
            for dep in self.source_dependencies:
                if not dep in self.srcgen:
                    real_src_files.append(dep)

        return real_src_files

    def write(self):
        """Writes the Make rules to compile this project to the Makefile."""

        # executable make target for building this library
        rule(
            output=self.name.replace(':', '_'),
            input=self.summary_file,
            phony=True)

        # Remove the file on compilation failure. Otherwise, running
        # make twice in a row will cause the second run to skip building
        # the broken library.
        trailing_opt = ' ' + self.project_file

        env_vars = 'LOGICBLOX_HOME=$(logicblox) '

        rule(
            output=[self.summary_file, self.outdir],
            input=self.source_dependencies + self.library_dependencies,
            commands=[
                'mkdir -p %s' % self.outdir,
                "%s sh -c '$(logicblox)/bin/lb compile project --libpath %s --out-dir %s' || ( rm -f %s; exit 1)"
                % (env_vars, self.libpath, self.outdir + trailing_opt, self.summary_file),
                'touch %s' % self.summary_file
            ] + self.post_cmds,
            description='Compiling logicblox project ' + self.name)

        if self.install:
            install_dir(self.outdir, self.install_subdir + '/' + self.name.replace(':', '_'))

        core.emit_clean_dir(os.path.dirname(self.summary_file))


def check_ws_success_file(ws_name):
    target = core.lb_workspace_target(ws_name)
    return '$(build)/check_workspace_%s.success' % target


def archive_export_target(ws_name):
    return core.get_ws_archive_names(ws_name)[1]


## private
class Workspace(object):
    """Represents an LB workspace and all the libraries to be installed. The
    object is responsible for writing out the Make rules to create a managed
    LB workspace."""

    def __init__(self, name, libraries=[], native_libs=[], archived=False, init_cmds=[], input=[], compress=True, create_cmd=None, keep=False):
        self.name = name
        self.libraries = libraries
        self.native_libs = native_libs
        # a list of all Projects to install. Used for getting proper libpaths.
        self.projects = []
        self.warnings=[]
        self.errors=[]
        # if the workspace should be exported and archived
        self.archived=archived
        # if the original workspace is to be kept (only used if archived is true)
        self.keep=keep
        self.init_cmds=init_cmds
        self.input=input
        # if the archived workspace should be compressed as tgz
        self.compress=compress
        self.create_cmd=create_cmd


    def populate(self):
        """Populates the projects attribute of this object. Must be run after
        all Projects have been created."""

        for lib in self.libraries:
            if lib in core.g_projects:
                self.projects.append(core.g_projects[lib])
            else:
                self.errors.append("Library %s, needed by workspace %s not  found."%(lib,self.name))
        if len(self.projects) > 1:
            self.warnings.append("Please specify at most 1 project to add to workspace \"%s\". Adding more than 1 project to the workspace can cause bad online performance and impact the size of the built workspace."%(self.name))

    def write(self):
        """Writes the Make rules to create the workspace to the Makefile."""

        success_file = check_ws_success_file(self.name)

        inputs = []
        if self.create_cmd is not None:
            create_cmd = self.create_cmd
        else:
            create_cmd = '$(lb) create %s --overwrite' % self.name
            if len(self.native_libs) > 0:
                libs_arg = '--libs ' + ','.join(self.native_libs)
                create_cmd += ' ' + libs_arg

        # put the removal of the success file first so make will fail if one
        # of the commands fails
        rm_cmd = 'rm -f %s' % success_file
        commands = [rm_cmd, create_cmd]

        for project in self.projects:
            inputs.append(project.summary_file)
            commands.append('$(lb) addproject %s %s --libpath %s --commit-mode diskcommit' % (self.name, project.outdir, project.libpath))

        if self.init_cmds is not None:
            for c in self.init_cmds:
                commands.append(c)

        commands.append(core.touch(success_file))

        if self.input is not None:
            for d in self.input:
                inputs.append(d)

        rule(
            output=success_file,
            input=inputs,
            commands='&&'.join(commands),
            description='Building workspace ' + self.name
        )

        emit_clean_workspace(self.name, success_file)

        check_target = core.check_lb_workspace_target(self.name)
        rule(
            output=check_target,
            input=success_file,
            phony=True
        )

        # if archived flag is true, generate a tgz file from the workspace and
        # delete the deployed workspace
        if self.archived:
            archive_names = core.get_ws_archive_names(self.name)
            ws_dir = archive_names[0]
            ws_export = archive_names[1]
            ws_archive = archive_names[2]

            archive_cmds = []
            archive_cmds.append('mkdir -p ' + ws_dir)
            archive_cmds.append('$(lb) export-workspace --overwrite ' + self.name + ' ' + ws_export)
            if not self.keep:
                archive_cmds.append('$(lb) delete ' + self.name)
            if self.compress:
                archive_cmds.append('(cd ' + ws_export + '; tar czf ../' + self.name + '.tgz *)')
                archive_cmds.append('rm -rf ' + ws_export)
                rule(
                    output=ws_export + '.tgz',
                    input=success_file,
                    commands='&&'.join(archive_cmds),
                    description='Archiving workspace ' + self.name
                )
                rule(
                    output='archive-ws-' + self.name,
                    input=ws_export + '.tgz',
                    phony=True
                )
                emit_clean_file(ws_archive)
            else:
                rule(
                    output=ws_export,
                    input=success_file,
                    commands='&&'.join(archive_cmds),
                    description='Archiving workspace ' + self.name
                )
                rule(
                    output='archive-ws-' + self.name,
                    input=ws_export,
                    phony=True
                )
                core.emit_clean_dir(ws_export)


# import workflow module for backwards compatibility
from workflow import *
