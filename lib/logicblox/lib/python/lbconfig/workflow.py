from api import *
import core


lb_workflow_dep = (
    "lb_workflow", {'default_path': "$LB_WORKFLOW_HOME",
                    'help': "The lb-workflow installation to use for this build."})

#
# LB-WORKFLOW DIRECTIVES
#

def lb_workflow_library(name, workflows_by_name={}, workflows=[], deps=[],
  active=[], execute=[], sources_root='src/wf', extensions=[], logic_only=False):
  '''Build a library with code generated for workflows.

  @param name
      The library name.

  @param workflows_by_name
      A map of workflow specifications keyed by the workflow name. The value of this map
      can either be a string (in which case it should be the name of the file that contains
      the workflow definition and its main workflow), or a dict specifying the workflow. This
      set must contain a 'filename' key that points to the workflow file; it may optionally
      also have a 'main' entry with the name of the main workflow and a 'params' entry with
      a list of parameters to pass to the workflow. See lb_workflow_gen for details on the
      main and params arguments.

      All workflow files are resolved relative to the sources_root parameter.

  @param workflows
      A list of workflow names. This is a convenience parameter for when the name of
      the workflow is the same as its filename and there are no configurations for the
      main workflow name and no parameters. The names in this list will be appended
      to the map in the workflows_by_name parameter and will thus be resolved relative
      to the sources_root parameter.

  @param deps
      A list of libraries that the workflow library depends upon. This is often the
      name of a library that contains logic to configure the workflow.

  @param active
      A list of files that contain active logic to install in the project.

  @param execute
      A list of files that contain logic to be executed when the library is installed
      in a workspace.

  @param sources_root
      The directory used as the root to resolve workflow files. This is not only
      used to resolve the workflows that will be generated in the library, but also
      to lookup additional workflow files (.wf files) that the Makefile rule will
      depend upon. This ensures that the library is regenerated when any workflow
      file in the sources_root changes.

  @param extensions
      List of extension directories to be passed to lb workflow.

  @param logic_only
      If true, the generator will generate delta logic that, when executed, will
      populate the schema corresponding to the workflow. If false, it will
      generate CSV files with data corresponding to the workflow, and the logic
      will contain only rules to load the CSV files into the schema. The
      data-based approach is faster to install, but it has a limitation: if
      generated as a module, it can only be installed separately into a
      workspace, i.e. it cannot be recursively loaded by some other project.
  '''

  # validate the name
  if ' ' in name:
      raise core.ConfigureError("lb_workflow_library: name must not have spaces: %s." % name)

  # collect all workflows under sources_root; if any change, we will rebuild the library
  wf_sources=core.find_files(sources_root, '.wf')

  # will generate code in these places
  generated_sources_root = "$(build)/logiql/workflow"
  generated_module = "%(generated_sources_root)s/%(name)s" % locals()
  generated_project_file = "%(generated_sources_root)s/%(name)s.project" % locals()

  # compute the workflows to generate
  workflows_map = dict(workflows_by_name)
  workflows_map.update(dict((name, name + '.wf') for name in workflows))
  if len(workflows_map) == 0:
      raise core.ConfigureError("lb_workflow_library: no workflows found; use 'workflows_by_name' or 'workflows' parameters.")

  # generate logic for each workflow under the generated_sources_dir
  generated_files = []
  for workflow_name, workflow_file in workflows_map.iteritems():
      if isinstance(workflow_file, dict):
          if not 'filename' in workflow_file:
              raise core.ConfigureError("lb_workflow_library: 'workflows_by_name' entry keyed by '%s' contains a set without a 'filename' key." % workflow_name)

          filename = workflow_file['filename']
          main_workflow = workflow_file['main'] if 'main' in workflow_file else None
          params = workflow_file['params'] if 'params' in workflow_file else []
          generated_files += lb_workflow_gen(sources_root + "/" + filename,
            workflow_name, generated_module, name, main_workflow, params,
            extensions=extensions, logic_only=logic_only)
      else:
          generated_files += lb_workflow_gen(sources_root + "/" + workflow_file,
            workflow_name, generated_module, name, extensions=extensions,
            logic_only=logic_only)


  libraries = ''.join([('%s, library\\n' % dep) for dep in deps])
  addblock = ''.join([('%s,  active\\n' % block) for block in active])
  execblock = ''.join([('%s,  execute\\n' % block) for block in execute])
  project_file_contents = """
      %(name)s, projectname
      lb_workflow, library
      status_service, library
      %(addblock)s
      %(execblock)s
      %(libraries)s
      %(name)s, module"""[1:].replace('\n', '\\n').replace(' ', '') % locals()

  # generate a project file
  copy_active = ''.join([('@cp %s/%s %s' % (sources_root, block, generated_sources_root)) for block in active])
  generated_files.extend([(sources_root + "/" + block) for block in active])
  copy_execute = ''.join([('@cp %s/%s %s' % (sources_root, block, generated_sources_root)) for block in execute])
  generated_files.extend([(sources_root + "/" + block) for block in execute])

  rule(generated_project_file, wf_sources + generated_files, [
      '@mkdir -p %(generated_sources_root)s' % locals(),
      '%(copy_active)s' % locals(),
      '%(copy_execute)s' % locals(),
      '@printf "%(project_file_contents)s" > %(generated_project_file)s' % locals()
  ])

  dependencies = dict((d, '$(%s)' % d) for d in deps)
  dependencies.update({ 'lb_web': '$(lb_web)', 'lb_workflow': '$(lb_workflow)' })

  # define a library with the generated workflows
  lb_library(
    name   = name,
    srcdir = generated_sources_root,
    deps = dependencies,
    generated = True,
    # copy auxiliary csvs into the compiled project, inside the module directory
    post_cmds = ['cp %s/*.csv $(build)/sepcomp/%s/%s' % (generated_module, name, name)]
  )

  # now wire dependencies: the library needs the project file and the workflow code
  rule("$(build)/sepcomp/" + name + "/LB_SUMMARY.lbp", generated_files + [generated_project_file])

  # rules to cleanup
  core.emit_clean_dir(generated_sources_root)


def lb_workflow_run(workflow_file, name=None, container='run-workflow', workspace='/workflow', auto_terminate=1,
  overwrite=True, active=[], execute=[], libraries=[], deps=[], bindings=[], init=[], targets=[], params=[],
  extensions=[]):
  '''Generate a phony target to run a workflow directly from the specification.

  @param workflow_file
      The file that contains the workflow specification.

  @param name
      The name that will identify the workflow in the workspace. By default, use the
      basename of the workflow_file.

  @param container
      The prefix of the generated phony target. The target will be container-name.

  @param workspace
      The name of the workspace used to install the workflow.

  @param auto_terminate
      If not None, instruct the lb-workflow driver to terminate automatically when there's this number
      of pollings without work to do.

  @param overwrite
      Whether is is OK to overwrite the workspace if it already exists.

  @param active
      An optional list of logic files to be added as active logic to the workspace before running the workflow.

  @param execute
      An optional list of logic files to be executed on the workspace before running the workflow.

  @param libraries
      An optional list of directories that contain LogiQL libraries to be installed in the workspace before
      running the workflow.

  @param deps
      An optional list of libraries that the workflow library depends upon. This assumes the libraries are built
      by the same Makefile. They will be added as Makefile targets and to the libraries list.

  @param bindings


  @param init
      An optional list of shell commands to be executed by the phony target before running the workflow.

  @param targets
      An optional list of Makefile targets that the phony target depends on.

  @param params
      A list of strings to be appended as parameters to the main workflow. Each entry should have the
      format 'parameter=value'.

  @param extensions
      List of extension directories to be passed to lb workflow.

  @param logic_only
      If true, the generator will generate delta logic that, when executed, will
      populate the schema corresponding to the workflow. If false, it will
      generate CSV files with data corresponding to the workflow, and the logic
      will contain only rules to load the CSV files into the schema. The
      data-based approach is faster to install, but it has a limitation: if
      generated as a module, it can only be installed separately into a
      workspace, i.e. it cannot be recursively loaded by some other project.

  @return a list of logic files that will be generated for the workflow once the
      rule is executed.
  '''

  workflow_name=name if name is not None else os.path.basename(workflow_file)

  dependencies = list(targets)
  dependencies.extend(deps)

  libraries_to_install = list(libraries)
  for dep in deps:
      libraries_to_install.append('$(build)/sepcomp/%s' % dep)


  command = '$(logicblox)/bin/lb workflow run --name %(name)s -f %(workflow_file)s --workspace %(workspace)s' % locals()
  if overwrite:
      command += ' --overwrite'
  if auto_terminate is not None:
      command += ' --auto-terminate %s' % auto_terminate
  for block in active:
      command += ' --addblock %s' % block
  for block in execute:
      command += ' --exec %s' % block
  for lib in libraries_to_install:
      command += ' --library %s' % lib
  for binding in bindings:
      command += ' --binding %s' % binding
  for param in params:
    command += ' --param %s' % param
  for extension in extensions:
    command += ' --extension %s' % extension

  commands = list(init)
  commands.append(command)

  rule('%s-%s' % (container, workflow_name), dependencies, commands, phony=True)


def lb_workflow_gen(workflow_file, name, outdir, module=None, main=None, params=[],
  extensions=[], logic_only=False):
  '''Generate logic for a workflow specification.

  @param workflow_file
      The file that contains the workflow specification.

  @param name
      The name that will identify the workflow in a workspace. By default, use the
      basename of the workflow_file.

  @param outdir
      The directory that will contain the generated sources.

  @param module
      The name of the module that contains the logic. This is often some trailing part of the outdir.
      If None, the outdir will be used.

  @param main
      The name of the main workflow declaration. If left as None, then the workflow_file must
      contain a workflow called "main".

  @param params
      A list of strings to be appended as parameters to the main workflow. Each entry should have the
      format 'parameter=value'.

  @param extensions
      List of extension directories to be passed to lb workflow.

  @return a list of logic files that will be generated for the workflow once the
      rule is executed.
  '''

  workflow_name=name if name is not None else os.path.basename(workflow_file)

  block_name = workflow_name.replace('-', '_').replace(' ', '_')
  module_name = outdir if (module is None) else module
  main_workflow = 'main' if (main is None) else main
  logic_only_cmd = ' --logic-only' if logic_only else ''
  parameters = ''.join([' --param %s' % p for p in params])
  extensions_cmd = ''.join([' --extension %s' % e for e in extensions])

  # the code that is generated from the workflow specification
  workflow_code = ['%(outdir)s/%(block_name)s.logic' % locals(),
                   '%(outdir)s/%(block_name)s_data.logic' % locals()]

  # rule to generate code when the specification changes
  rule(workflow_code, [ workflow_file ],
      [ '$(logicblox)/bin/lb workflow generate -f %(workflow_file)s -o %(outdir)s -b %(block_name)s --module-name %(module_name)s --name %(workflow_name)s%(logic_only_cmd)s --main %(main_workflow)s%(parameters)s%(extensions_cmd)s' % locals() ],
      description = 'Generating code for workflow defined in "%s" with main "%s"' % (workflow_file, main_workflow)
  )

  # rules to cleanup
  for f in workflow_code:
      emit_clean_file(f)

  return workflow_code


def lb_workflow_doc(workflow_file, title='Workflow Documentation',
  outdir='$(build)/doc/workflows', target='workflow-doc', install=True,
  isdir=False, extensions=[]):
  '''Generate documentation for a workflow specification.

     This directive will create a new phony target that can be used to generate the documentation manually (make $target). If install
     is true, the documentation will be installed in 'make install'.

  @param workflow_file
      The file that contains the workflow specification that generates the index.html root documentation file. It is common to create
      an artificial workflow file (say, readme.wf) that simply imports all main workflows of the project and provides an overview of
      them via documentation blocks.

  @param title
      The title of the documentation, used as the header in the HTML pages.

  @param outdir
      The directory that will contain the generated documentation.

  @param target
      The name of the phony Make target

  @param install
      If true, install the documentation when doing 'make install'.

  @param isdir
      If true, workflow_file is treated as a directory and the target will generate documentation for
      every .wf file found in that directory.

  @param extensions
      List of extension directories to be passed to lb workflow.

  '''
  # rule to generate documentation for the workflows
  if isdir:
    input_param = ' --input-dir %s' % workflow_file
  else:
    input_param = ' -f %s' % workflow_file

  extensions_cmd = ''.join([' --extension %s' % e for e in extensions])

  rule(outdir, [workflow_file],
    ['$(logicblox)/bin/lb workflow doc -o ' + outdir + input_param + ' --title "' + title + '" %s' % extensions_cmd]
  )
  rule(target, outdir,
    phony=True
  )
  if install:
      rule('install', target)
      install_dir(outdir, 'share/doc/workflows')

  # cleanup documentation in make clean
  core.emit_clean_dir(outdir)



def lb_workflow_workspace(name, libraries=[], init_cmds=[]):
  '''Generate a rule to create an empty lb-workflow workspace. The workspace will contain only
     the libraries needed by lb-workflow, such as lb-web, lb-workflow, and status library.

  @param name
      The name of the workspace to create.

  @param libraries
      List of libraries that should be installed when the workspace is created.

  @param init_cmds
      An optional list of commands to be executed after the workspace is
      created and libraries are installed but before the workspace is
      exported.
  '''
  check_lb_workspace(
    name = name,
    libraries = libraries,
    init_cmds = init_cmds,
    create_cmd = '$(logicblox)/bin/lb workflow create --workspace %s --overwrite --load-services false' % name
  )

#
# Declaration of the jar dependencies of lb-workflow. This may be needed by
# extensions that need to link to lb-workflow dependencies. By providing these
# variables we ensure that we can manage these dependencies in a single place.
#
jetty_version = '7.6.7.v20120910'
lb_workflow_build_deps = [
  # lb workflow itself
  '$(lb_workflow)/lib/java/lb-workflow.jar',
  '$(lb_workflow)/lib/java/lb-workflow-tasks.jar',

  # logicblox dependencies
  '$(lb_web)/lib/java/datalog-generator.jar',
  '$(lb_web)/lib/java/lb-common.jar',
  '$(lb_web)/lib/java/lb-common-protocol.jar',
  '$(lb_web)/lib/java/lb-web-client.jar',
  '$(lb_web)/lib/java/lb-web-server.jar',
  '$(lb_web)/lib/java/s3lib-0.2.jar',

  # third party dependencies
  '$(logicblox)/lib/java/commons-io-2.4.jar',
  '$(logicblox)/lib/java/lb-connectblox.jar',
  '$(lb_web)/lib/java/annotations.jar',
  '$(lb_web)/lib/java/commons-codec-1.9.jar',
  '$(lb_web)/lib/java/commons-configuration-1.8.jar',
  '$(lb_web)/lib/java/commons-lang-2.6.jar',
  '$(lb_web)/lib/java/gson-2.2.4.jar',
  '$(lb_web)/lib/java/guava-15.0.jar',
  '$(lb_web)/lib/java/httpcore-4.3.3.jar',
  '$(lb_web)/lib/java/jcommander-1.29.jar',
  '$(lb_web)/lib/java/jetty-client-' + jetty_version +'.jar',
  '$(lb_web)/lib/java/jetty-http-'   + jetty_version +'.jar',
  '$(lb_web)/lib/java/jetty-io-'     + jetty_version +'.jar',
  '$(lb_web)/lib/java/jetty-util-'   + jetty_version +'.jar',
  '$(lb_web)/lib/java/joda-time-2.8.1.jar',
  '$(lb_web)/lib/java/log4j-1.2.13.jar',
  '$(lb_web)/lib/java/protobuf-2.6.1.jar',
  '$(lb_web)/lib/java/scala-library.jar',

  '$(lb_web)/lib/java/commons-logging-1.1.3.jar',
  '$(lb_web)/lib/java/aws-java-sdk-1.10.20.jar',
  '$(lb_web)/lib/java/httpclient-4.3.6.jar',
  '$(lb_web)/lib/java/jackson-annotations-2.5.3.jar',
  '$(lb_web)/lib/java/jackson-core-2.5.3.jar',
  '$(lb_web)/lib/java/jackson-databind-2.5.3.jar',

  '$(logicblox)/lib/java/junit-4.8.2.jar',

  # s3lib, GCS dependencies
  '$(lb_web)/lib/java/google-api-services-storage-v1-rev26-1.19.1.jar',
  '$(lb_web)/lib/java/google-api-client-1.19.1.jar',
  '$(lb_web)/lib/java/google-oauth-client-1.19.0.jar',
  '$(lb_web)/lib/java/google-http-client-1.19.0.jar',
  '$(lb_web)/lib/java/google-http-client-jackson2-1.19.0.jar',
  '$(lb_web)/lib/java/jsr305-1.3.9.jar',
]
lb_workflow_test_deps = lb_workflow_build_deps

def lb_workflow_extension(name, srcdir='src',
  module=None, java_tests_main=None, python_tests=[], jars=[]):
  '''Declare an lb workflow extension.

  This directive is very opinionated on how you should structure your
  extension's code (see srcdir param). If you would like a custom organization,
  you look at this method for inspiration.

  @param name
    The name of the extension.

  @param srcdir
    The directory where the sources of the extension is located. This directory
    must have a 'main/wf' subdirectory with the extension's workflow code. It
    may contain a 'main/java' subdirectory with java implementation of custom
    tasks. It may also contain a 'test/java' subdirectory with junit tests, but
    this is only used if junit_main_suite is declared.

  @param jars
    Path to jars that are required by the extension's java code. These jars will
    be added to the classpath when compiling java, and will be installed
    together with the generated jar so that it is added to the classpath at
    runtime.

  @param module
    If the extension contains a single module this parameter can be set to the
    name of that module. In this case, documentation is generated only for this
    module; otherwise, an index will be generated for all modules in the
    extension.

  @param java_tests_main
    The absolute classname of the a main java class that sets up and executes
    tests for the custom task implementations. This is often a JUnit runner.

  @param python_tests
    An array of python scripts that contain testcases for the extension. These
    testcases often require the extension to be installed, so when they are
    present, the check target will depend on install, which is assumed to be
    idempotent. This support is only for basic standalone testcases; if your
    testcase requires a richer context, such as building a workspace, you may
    want to declare it independently using check_program.
  '''

  # the dependencies include the testing jars plus whatever the extension needs
  jar_deps = lb_workflow_test_deps + jars

  # add a target to create links to dependencies
  link_libs(jar_deps)

  # only generate a jar target if there's actually some java code, which is only
  # needed if there's a custom task implementation.
  if os.path.exists('%s/main/java' % srcdir):
    jar(
      name = name,
      srcdir = '%s/main/java' % srcdir,
      classpath = jar_deps
    )

  # install external dependencies
  for j in jars:
    install_file(j, 'lib/java')

  # target for a junit test suite
  if java_tests_main is not None:
    check_jar(
      name = '%s-tests' % name,
      main = java_tests_main,
      srcdirs = ['%s/test/java' % srcdir],
      deps = [name],
      classpath = jar_deps
    )

  # python tests
  for test in python_tests:
    # make sure we make install before check
    rule('check', 'install')
    check_program(test)

  # there must always be some workflow code
  install_dir('%s/main/wf' % srcdir, 'lib/wf')

  # with proper documentation
  if module is None:
    lb_workflow_doc(
      '%s/main/wf' % srcdir,
      title="Documentation for '%s' Extension" % name,
      isdir=True)
  else:
    lb_workflow_doc(
      '%s/main/wf/%s.wf' % (srcdir, module),
      title="Documentation for '%s' Extension" % name)
