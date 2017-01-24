#!/usr/bin/env python

import sys
import os
import argparse
import cli.lbparser
thisdir = os.path.dirname(os.path.realpath(__file__))
prefix = os.path.dirname(os.path.dirname(os.path.dirname(thisdir)))

from cli import util

LB_WORKFLOW_DEFAULT_WORKSPACE=os.environ.get("LB_WORKFLOW_DEFAULT_WORKSPACE", "/workflow")
LB_WORKFLOW_SERVICES=os.environ.get("LB_WORKFLOW_SERVICES", "http://localhost:55183")

def run(args, extra, command_line):
    # most dependencies are already in the manifest, but we need to add some here
    deps = [
      'lb-workflow.jar',
      'lb-workflow-tasks.jar',
      'handlers/bloxweb-connectblox.jar'
    ]
    deps_paths = [prefix + '/lib/java/' + name for name in deps]

    subenv = os.environ.copy()
    subenv['LB_WORKFLOW_HOME'] = prefix

    if os.environ.get('LB_DEPLOYMENT_HOME') is None:
        from os.path import expanduser
        subenv['LB_DEPLOYMENT_HOME'] = os.path.join(expanduser("~"), "lb_deployment")

    # load the configuration files
    config_dirs = [prefix + '/config', util.get_lb_deployment_home() + '/config']
    config = util.load_global_config('lb-workflow-driver', directories=config_dirs)
    try:
      if args.config:
        config.read(args.config)
    except AttributeError:
      pass

    # get directories configured to be extensions
    extensions=[]
    try:
      if args.extension:
        extensions.extend(args.extension)
    except AttributeError:
      pass
    if config.has_option('global', 'extension_dirs'):
      extensions.extend(config.get('global', 'extension_dirs').strip().split(','))
    extensions = [x for x in extensions if x is not '']

    # find jars in the extensions and add to the front of the CLASSPATH
    for extension in extensions:
      java_dir = ('%s/lib/java' % extension).strip()
      if os.path.isdir(java_dir):
        for f in os.listdir(java_dir):
            if f.endswith(".jar"):
              deps_paths.insert(0, '%s/%s' %(java_dir, f))

    classpath = ':'.join(deps_paths)
    java_args = ['java', '-cp', classpath]

    if 'jvm-args' in args:
        java_args.extend(args.jvmArgs.split())
    java_args.extend(['com.logicblox.workflow.Main'])
    java_args.extend(command_line[1:])

    os.execvpe('java', java_args, subenv)

def add_workflow_commands(subparser):
    # Create a list for sub-commands
    more_subparsers = subparser.add_subparsers(title='workflow commands')

    # Use better formatter for commands, and use the standard of
    # invoking the function cmd_{subcommand}
    def add_command(cmd, help, description=None):
        p = more_subparsers.add_parser(cmd, help=help,description=description,formatter_class=cli.lbparser.CLICommandHelpFormatter)
        p.set_defaults(extra_func=run)
        return p

    def workflow_file_options(p, file_required=True):
        p.add_argument('-f','--file',
                       dest="filename",
                       required=file_required,
                       help="the file containing the main workflow specification source")
        p.add_argument('-m','--main',
                       dest="mainWorkflow",
                       default = "main",
                       help="the name of the main workflow declaration")

    def workflow_parameters_option(p):
        p.add_argument('--param',
                       dest="params",
                       nargs="*",
                       help="""string in the form 'parameter=value' to be passed to the main workflow.""")

    def workflow_name_option(p):
        p.add_argument('--name',
                       dest="workflowName",
                       default="default",
                       help="name of the workflow, to be used in the workspace to distinguish different workflows")

    def workspace_name_option(p):

        p.add_argument('-w','--workspace',
                       dest="workspaceName",
                       default=LB_WORKFLOW_DEFAULT_WORKSPACE,
                       help="the name of the workspace; the default may be set with the "\
                       "LB_WORKFLOW_DEFAULT_WORKSPACE environment variable (default: %s)" % LB_WORKFLOW_DEFAULT_WORKSPACE)

    def deprecated_workspace_name_option(p):

        p.add_argument('-w','--workspace',
                       dest="workspaceName",
                       help="this parameter is ignored because the command now uses the control service [deprecated]")

    def workspace_name_list_option(p):

        p.add_argument('-w','--workspace',
                       dest="wsnames",
                       nargs="+",
                       default=[LB_WORKFLOW_DEFAULT_WORKSPACE],
                       help="the name of the workspace; the default may be set with the "\
                       "LB_WORKFLOW_DEFAULT_WORKSPACE environment variable (default: %s)" % LB_WORKFLOW_DEFAULT_WORKSPACE)

    def compiler_option(p):
        p.add_argument('--no-warnings',
                       dest="noWarnings",
                       action="store_true",
                       help="avoid printing compilation warnings")

    def workspace_overwrite_option(p):
        p.add_argument('--overwrite',
                       dest="overwrite",
                       action="store_true",
                       help="overwrite existing workspace if it exists")

    def driver_messenger_options(p):
        p.add_argument('--commit-mode',
                       dest="commitMode",
                       default="diskcommit",
                       help="commit mode for inactive blocks: diskcommit or softcommit")
        p.add_argument('--max-retries',
                       dest="maxRetries",
                       default=-1,
                       help="maximum number of times to attempt to connect to lb-server before giving up")


    def deprecated_driver_messenger_options(p):
        p.add_argument('--commit-mode',
                       dest="commitMode",
                       help="this parameter is ignored because the command now uses the control service [deprecated]")
        p.add_argument('--max-retries',
                       dest="maxRetries",
                       help="this parameter is ignored because the command now uses the control service [deprecated]")


    def load_services_option(p):
        workspace_name_option(p)
        p.add_argument('--load-services',
                       dest="load_services",
                       action="store_true",
                       help=argparse.SUPPRESS)
        p.add_argument('--no-load-services',
               dest="load_services",
               action="store_true",
               help="do not automatically load the services of the new workspace in lb-web (default: false)")

    def service_libs_option(p):
        # service libraries are now in core; keeping here to avoid breaking the cmdline
        p.add_argument('--no-service-libs',
                       dest="noServiceLibs",
                       action="store_true",
                       help=argparse.SUPPRESS)
    def bindings_option(p):
        p.add_argument('--binding',
                       dest="binding",
                       nargs="*",
                       help="""a string in the form 'predicate=value'.
This will generate a string scalar predicate with this name, install it
in the workflow workspace and set its value
                       """)
    def driver_timing_options(p):
        p.add_argument('--frequency',
                       dest="frequency",
                       default=60,
                       help="polling frequency is seconds")
        p.add_argument('--auto-terminate',
                       dest="autoTerminate",
                       default=-1,
                       help="automatically terminate driver after not having work to do for N polling actions")

    def profiling_option(p):
        p.add_argument('--profile',
                       dest="profile",
                       action="store_true",
                       help="generate profile information for the execution")

    def extensions_option(p):
        custom_config_option(p)
        p.add_argument('--extension',
                       dest="extension",
                       nargs="*",
                       help="a directory that contains an lb workflow extension")

    def custom_config_option(p):
        p.add_argument('--config',
                       dest="config",
                       help="custom lb-workflow-driver.config to refine the default configuration file")

    def driver_options(p):
        driver_timing_options(p)
        driver_messenger_options(p)
        profiling_option(p)
        extensions_option(p)
        p.add_argument('--jvm-args',
                       dest="jvmArgs",
                       help="arguments to pass to the JVM. Need to be between quotes")


    def state_options(p):
        p.add_argument('-s','--state','--states',
                       dest="state",
                       nargs="*",
                       help="select only task instances that are in one of these task states")
        p.add_argument('--executing',
                       dest="executing",
                       action="store_true",
                       help="select tasks that are in the task state 'Executing'; alias to '--state Executing'")
        p.add_argument('--failed',
                       dest="failed",
                       action="store_true",
                       help="select tasks that are in the task state 'Failed'; alias to '--state Failed'")
        p.add_argument('--failed-restartables',
                       dest="failed",
                       action="store_true",
                       help="select restartables that have children tasks that are in the task state 'Failed'")
        p.add_argument('--aborted',
                       dest="aborted",
                       action="store_true",
                       help="select tasks that are in the task state 'Aborted'; alias to '--state ABORTED'")
        p.add_argument('--end',
                       dest="succesful",
                       action="store_true",
                       help="select tasks that are in the task state 'End'; alias to '--state END'")

    def status_service_info(p):
        default = "%s/status" % LB_WORKFLOW_SERVICES
        p.add_argument('-u','--status-service-uri',
                       dest="uri",
                       default=status,
                       help="the URI of the status service used to get workflow status information; "\
                       "the LB_WORKFLOW_SERVICES environment variable can be used to set the default "\
                       "prefix for workflow services (default: %s)" % default)

    def control_service_info(p):
        default = "%s/control" % LB_WORKFLOW_SERVICES
        p.add_argument('-c','--control-service-uri',
                       dest="uri",
                       default=default,
                       help="the URI of the status service used to get workflow status information; "\
                       "the LB_WORKFLOW_SERVICES environment variable can be used to set the default "\
                       "prefix for workflow services (default: %s)" % default)

        default_timeout = 320
        p.add_argument('-T','--timeout',
                       dest="timeout",
                       default=default_timeout,
                       help="the timeout when invoking the control service, in seconds "\
                       "(default: %ss)" % default_timeout)

    def raw_or_json(p):
        g = p.add_mutually_exclusive_group()
        g.add_argument('--raw',
                       dest = "raw",
                       help="get info from the raw protobuf response in this file")
        g.add_argument('--json',
                       dest = "json",
                       help="get info from the json protobuf response in this file")

    def raw_or_json_print(p):
        g = p.add_mutually_exclusive_group()
        g.add_argument('--raw',
                       action = "store_true",
                       help="Print the raw protobuf response from the status service instead of pretty-printing")
        g.add_argument('--json',
                       action = "store_true",
                       help="Print the raw json response from the status service instead of pretty-printing")

    def run_options(p):
        workflow_file_options(p)
        workflow_name_option(p)
        workflow_parameters_option(p)
        bindings_option(p)
        workspace_overwrite_option(p)
        compiler_option(p)
        load_services_option(p)
        service_libs_option(p)
        driver_options(p)
        p.add_argument('--addblock',
                         dest="addblock",
                         help="a file containing active logic to be added to the workspace before installing the workflow")

        p.add_argument('--library',
                         dest="library",
                         help="a directory containing a pre-compiled logic library to be added to the workspace before installing the workflow")

        p.add_argument('--exec',
                         dest="exec",
                         help="a file containing logic to be executed in the workspace before installing the workflow, but after installing blocks and libraries")
        p.add_argument('-q', '--quick',
                         action = "store_true",
                         help="a convenience flag to quickly execute a workflow file; equivalent to --overwrite --auto-terminate 1 and setting the default" +
                         " worspace to /workflow@run so that a branch is used.")

    gen = add_command('generate',help='generate LogiQL from a workflow specification')
    gen.add_argument('-o','--out-dir',
                     dest="outdir",
                     default="<stdout>",
                     help="the directory in which to place the generated logic")
    gen.add_argument('-b','--block-name',
                     dest="blockName",
                     default="flow",
                     help="the name of the block that will contain the generated code")
    gen.add_argument('--module-name',
                     dest="moduleName",
                     default="flow",
                     help="the name of the module that will contain the generated code. By default use --out-dir")

    gen.add_argument('--inactive',
                     dest="inactive",
                     action="store_true",
                     help="whether the generated block should be 'inactive' instead of the default 'execute'")

    gen.add_argument('--legacy',
                     dest="legacy",
                     action="store_true",
                     help="generate legacy logic - no modules")

    gen.add_argument('--check',
                     dest="check",
                     action="store_true",
                     help="do not generate logic, just check the source for errors")

    gen.add_argument('--logic-only',
                     dest="logic_only",
                     action="store_true",
                     help="generate pure logic instead of CSVs and logic")

    gen.add_argument('--debug',
                     dest="debug",
                     action="store_true",
                     help=argparse.SUPPRESS)
    gen.add_argument('--input-dir',
                     dest="input-dir",
                     required=False,
                     help="directory to lookup for workflow files. This will generate logiQL for all .wf files (recursively)")

    workflow_file_options(gen, False)
    workflow_name_option(gen)
    compiler_option(gen)
    extensions_option(gen)

    check = add_command('check',help='check a workflow specification')
    check.add_argument('--input-dir',
                     dest="input-dir",
                     required=False,
                     help="directory to lookup for workflow files. This will check all .wf files (recursively)")
    workflow_file_options(check, False)
    compiler_option(check)
    extensions_option(check)

    create = add_command('create',help='create an empty workflow workspace')
    workspace_overwrite_option(create)
    driver_messenger_options(create)
    load_services_option(create)
    service_libs_option(create)
    profiling_option(create)
    compiler_option(create)
    extensions_option(create)

    install = add_command('install',help='install workflow in a workspace')
    workflow_file_options(install)
    workflow_name_option(install)
    workflow_parameters_option(install)
    workspace_name_option(install)
    bindings_option(install)
    driver_messenger_options(install)
    extensions_option(install)

    start = add_command('start',help='start executing a workflow')
    workflow_name_option(start)
    workflow_parameters_option(start)
    control_service_info(start)
    deprecated_workspace_name_option(start)
    deprecated_driver_messenger_options(start)

    status = add_command('status',help='print status of a workflow')
    state_options(status)
    status_service_info(status)
    raw_or_json_print(status)
    workflow_name_option(status)
    status.add_argument('--show-empty-instances',
                        dest="showEmptyInstances",
                        action = "store_true",
                        help="also list workflow instances that have no process instances selected")
    status.add_argument('--root',
                        dest="root",
                        help="""the Id of the process instance that is the root of the workflow to get status.
If undefined, get from all roots of the selected workflow
                        """)
    status.add_argument('-n','--process-name',
                        dest="processName",
                        help="name of the process to get information from. By default, get from all processes")
    status.add_argument('-id','--id',
                        nargs="*",
                        dest="processInstanceId",
                        help="the Id of the process instance to get information from. By default, get from all instances")
    status.add_argument('--all',
                        dest="all",
                        action = "store_true",
                        help="get information from all instances, instead of only from instances that have begun")
    status.add_argument('--no-actions',
                        dest="noReceptiveActions",
                        action = "store_true",
                        help="do not get information about which actions a process is receptive to")
    status.add_argument('--vars',
                        dest="instanceVars",
                        action = "store_true",
                        help="get information about instance variable bindings")
    status.add_argument('--no-io',
                        dest="noIO",
                        action = "store_true",
                        help="do not get information about inputs and output parameters of the process")
    status.add_argument('--history',
                        dest="history",
                        action = "store_true",
                        help="get task history of state transitions")
    status.add_argument('--source',
                        dest="source",
                        action = "store_true",
                        help="get complete information about the source code locations where processes were instantiated")
    status.add_argument('--list-states',
                        dest="listStates",
                        action = "store_true",
                        help="do not print status. Only list all available task state names, from all installed workflows")
    status.add_argument('--list-workflows',
                        dest="listWorkflows",
                        action = "store_true",
                        help="do not print status. Only list all installed workflows by name")
    status.add_argument('--list-roots',
                        dest="listRoots",
                        action = "store_true",
                        help="get information from  all root instances, including terminated ones")
    status.add_argument('--active-roots',
                        dest="activeRoots",
                        action = "store_true",
                        help="get information from root instances that are active (begun but did not terminate)")
    status.add_argument('--ancestors',
                        dest="ancestors",
                        action = "store_true",
                        help="always get ancestors of selected processes, making the process tree look complete")
    status.add_argument('--count',
                        dest="count",
                        action = "store_true",
                        help="do not return info, only the number of selected process instances, on line per selected workflow")
    status.add_argument('--ui',
                        dest="ui",
                        action = "store_true",
                        help="open a simple UI to visualize the workflows and process trees")
    status.add_argument('--complete',
                        dest="complete",
                        action = "store_true",
                        help="get the most complete information set possible. Same as --history --source --vars --all")
    status.add_argument('--actions',
                        dest="receptiveActions",
                        action = "store_true",
                        help="this option is the default and will be removed from future versions [deprecated]")
    status.add_argument('--io',
                        dest="io",
                        action = "store_true",
                        help="this option is the default and will be removed from future versions [deprecated]")


    purge = add_command('purge', help='purge terminated workflow instances that match the criteria')
    control_service_info(purge)
    purge.add_argument('--name',
                        dest="name",
                        help="""name of the workflow to be purged; only terminated instances of the
                        workflow with this name will be purged""")
    purge.add_argument('--root',
                        dest="root",
                        help="""id of the process instance that is the root of the workflow to purge;
                        if undefined, purge all roots that match the other criteria
                        """)
    purge.add_argument('--all',
                        dest="all",
                        action = "store_true",
                        help="request that all workflow instances be purged")
    purge.add_argument('--older-than',
                        dest="olderThan",
                        help="""purge workflows whose terminated timestamp is older than this duration
                        (e.g. '7d' or '2months')""")



    info = add_command('info',help='print information from a status report')
    raw_or_json(info)
    info.add_argument('--longest-tasks',
                        dest="longestTasks",
                        help="print the n tasks that took the longest in total, from begin to termination")
    info.add_argument('--longest-execution-tasks',
                        dest="longestExecutionTasks",
                        help="print the n tasks that took the longest in execution time")
    info.add_argument('--longest-non-tasks',
                        dest="longestNonExecutionTasks",
                        help="print the n tasks that took the longest in terms of time not executing")
    info.add_argument('--depth',
                        dest="depth",
                        action = "store_true",
                        help="print only the depth of the process tree")
    info.add_argument('--types',
                        dest="types",
                        action = "store_true",
                        help="print only a summary of the task types in the workflow")
    info.add_argument('--ui',
                        dest="ui",
                        action = "store_true",
                        help="open a simple UI to visualize the workflows and process trees")

    driver = add_command('driver',help='execute the workflow driver')
    driver_options(driver)
    workspace_name_list_option(driver)

    action_description="""RAW|
This command sends actions to the state machine of selected tasks. The action name is required. Most
of the other options are used to select which tasks to target. Suppose the 'retry' action is to be
sent. The target tasks can be selected:

  - by id (using --id):

      // send retry only to task with this id
      $COMMAND_NAME action -a retry --id 001

  - by workflow (using --global):

      // all tasks in the latest instance of the 'default' workflow
      $COMMAND_NAME action -a retry --global

      // all tasks in the latest instance of the 'batch' workflow
      $COMMAND_NAME action -a retry --global --name batch

      // all tasks in the workflow rooted by the task with this id
      $COMMAND_NAME action -a retry --global --root 001

  - by state (using --state or a shorthard state selector):

      // all failed tasks in the latest instance of the 'default' workflow
      $COMMAND_NAME action -a retry --state Failed

      // shorthand for the above
      $COMMAND_NAME action -a retry --failed

      // all failed tasks in the workflow rooted by the task with this id
      $COMMAND_NAME action -a retry --failed --root 001

      """
    action = add_command('action',help='execute an action towards selected processes',description=action_description)
    workflow_name_option(action)
    deprecated_workspace_name_option(action)
    profiling_option(action)
    state_options(action)
    control_service_info(action)
    action.add_argument('-a','--action',
                        required=True,
                        dest="action",
                        help="action to execute (e.g., 'retry' or 'ignore')")
    action.add_argument('-id','--id',
                        dest="processInstanceId",
                        help="the Id of the process instance to target the action")
    action.add_argument('--root',
                        dest="root",
                        help="""apply a global or state-based action only to processes that are descendants of the process with this id.
Takes precedence over workflow selection by --name and --source-workflow
                        """)
    action.add_argument('--source-workflow',
                        dest="sourceWorkflow",
                        help="""apply a global or state-based action only to processes that were
                        defined under the workflow with this name in the workflow source files
                        """)
    action.add_argument('--global',
                        dest="global",
                        action = "store_true",
                        help="the action is to be applied to every existing task")
    action.add_argument('--silent',
                        dest="silent",
                        action = "store_true",
                        help="do not print status information after the action is executed")
    action.add_argument('--commit-mode',
                       dest="commitMode",
                       default="diskcommit",
                       help="commit mode for inactive blocks: diskcommit or softcommit")

    run_cmd = add_command('run',help='run the given workflow (combines create, install, start, and driver)')
    run_options(run_cmd)

    replay = add_command('replay',help='replay the given workflow guided by the status report of a previous run')
    run_options(replay)
    raw_or_json(replay)

    doc = add_command('doc',help='generate documentation from a workflow specification')
    doc.add_argument('-f','--file',
                     dest="filename",
                     required=False,
                     help="the file containing the main workflow specification source. By default, generate stdlib documentation")
    doc.add_argument('--input-dir',
                     dest="input-dir",
                     required=False,
                     help="directory to lookup for workflow files. This will generate documentation for all .wf files (recursively)")
    doc.add_argument('-o','--out-dir',
                     dest="outdir",
                     help="the directory in which to place the generated documentation")
    doc.add_argument('--clean',
                        dest="clean",
                        action = "store_true",
                        help="cleanup the target directory before generation")
    doc.add_argument('--api',
                        dest="api",
                        action = "store_true",
                        help="generate interface documentation only (no workflow code)")
    doc.add_argument('--no-stdlib',
                        dest="noStdLib",
                        action="store_true",
                        help=argparse.SUPPRESS)
    doc.add_argument('--title',
                     dest="title",
                     default="LogicBlox Workflow Documentation",
                     help="set the title of the documentation")
    doc.add_argument('--no-page-title',
                        dest="noPageTitle",
                        action="store_true",
                        help="do not write a page title using the file name")
    doc.add_argument('--no-comment-title',
                        dest="noCommentTitle",
                        action="store_true",
                        help="do not write a title on the top of comment blocks")
    extensions_option(doc)




def main():
    command_line = sys.argv[1:]
    run(command_line)

if __name__ == '__main__':
    main()
