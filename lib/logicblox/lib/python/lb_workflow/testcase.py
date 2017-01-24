
import json
import subprocess
import threading

try:
    import unittest2 as unittest
except ImportError:
    import unittest

import lb.web.testcase


class WorkflowTestCase(lb.web.testcase.MultiplePrototypeWorkspacesTestCase):
  '''A testcase to support lb workflow tests.

  This is similar to a MultiplePrototypeWorkspacesTestCase where the prototypes
  are 1) a workspace that will contain a workflow and 2) an optional set of
  workspaces used by the workflow. All these prototypes will be branched prior
  to a test execution, and will have their services loaded.
  '''

  #
  # Class Level Members
  #

  # Sub-types must define the name of the workflow workspace as this prototype
  workflow_prototype = None

  # Sub-types may define a list (set) of support workspaces that will also be branched
  support_prototypes = []

  @classmethod
  def setUpClass(cls):
    # compute the full prototypes, which include support + the workflow prototype
    if cls.workflow_prototype is None:
      cls.workflow_prototype = '/workflow'
      subprocess.check_call('lb workflow create --overwrite --load-services false', shell=True)
    cls.prototypes = cls.support_prototypes + [cls.workflow_prototype]
    super(WorkflowTestCase, cls).setUpClass()

  #
  # Instance Level Members
  #

  # this value is set by the infrastructure with the full name to address the branch
  # created for the workflow prototype (e.g. "my_workspace@some_branch")
  workflow_workspace = None

  # client instances
  status_client = None
  control_client = None

  def setUp(self):
    super(WorkflowTestCase, self).setUp()
    self.workflow_workspace = self.workspaces[self.workflow_prototype]
    self.status_client = lb.web.service.Client("localhost", 55183, "/status")
    self.control_client = lb.web.service.Client("localhost", 55183, "/control")

  # override if you need a different client than the default
  def get_status_client(self, service="/status"):
    if service=="/status":
      return self.status_client
    return lb.web.service.Client("localhost", 55183, service)

  # override if you need a different client than the default
  def get_control_client(self, service="/control"):
    if service=="/control":
      return self.control_client
    return lb.web.service.Client("localhost", 55183, service)

  def get_status(self, request='{}', service="/status"):
    return json.loads(self.get_status_client(service=service).call_json(request))

  def print_status(self, request='{}', service="/status"):
    '''Print the status for debug'''
    self.pretty_print(self.get_status(request, service))

  def pretty_print(self, txt):
    print json.dumps(txt, sort_keys=True, indent=4, separators=(',', ': '))

  def resolve_status_workflow_instance(self, instance):
    '''Given a workflow instance returned from the status service, this function
    will resolve all parent-child relationships between nodes, possibly resolve
    io information, and will return the root node of the tree.

    The status service returns a linearization of the tree, where all nodes are
    in an array, and the children are referred to by id. This method will
    resolve all children by id in order to recompose the tree. The root node
    will be stored in instance['root'] and will be returned. Also, the
    'children' attribute of each node will be overwritten with an array that
    contains the resolved children nodes already sorted (by the 'order'
    returned by the status service).
    '''
    # first collect all process nodes by id and find the root
    root = None
    processes = dict()
    for process in instance['process']:
      if process['root']:
        root = process
      processes[process['id']] = process
      def resolve_io(io):
        new_io = dict()
        for i in io:
          if len(i['value']) == 1:
            new_io[i['key']] = i['value'][0]
          else:
            new_io[i['key']] = i['value']
        return new_io

      if 'input' in process:
        process['input'] = resolve_io(process['input'])
      if 'output' in process:
        process['output'] = resolve_io(process['output'])

    if root is None:
      raise Exception("Instance has no root")

    # now resolve process children, overwritting the children attribute
    for process in instance['process']:
      if 'children' in process:
        children = []
        for child in process['children']:
          p = processes[child['id']]
          # copy these attributes from reference object to node because they
          # may be useful
          p['order'] = child['order']
          p['relation_to_parent'] = child['relation_to_parent']
          children.append(p)

        # overwrite children, sorting by their order attribute
        process['children'] = sorted(children, key=lambda o: o['order'])

    # set the root and return it
    instance['root'] = root
    return root

  # TODO - the params argument should be an array of strings because {} does not
  # allow for multiple values to the same param
  def lb_workflow_run(self, filename, main='main', name='default', params={},
    debug=False, load_services=False, workspace=None,
    control_uri=None, extensions=[]):
    '''Execute an lb workflow.

      This will install the workflow defined by this filename and main parameters into the branch
      created for the workflow workspace. This workflow will then be started (an instance will be
      created) and an lb workflow driver will be executed to run the workflow.

      @param filename
        The full path to the file that contains the workflow to execute.

      @param main
        The name of the main workflow to execute.

      @param name
        The name of the workflow.

      @param params
        A dictionary with parameters to be passed to the main workflow.

      @param debug
        If true, print the standard output and error while executing the driver

      @param control_uri
        The URI of the control service to use (currently for starting the workflow).

      @param extensions
        List of directories to pass as workflow extensions.

      @return a tuple (retcode, stdout, stderr) with the return code, standard output printout and
        standard error printout for the driver process created to execute the workflow. If debug is
        True, then only the retcode contains data because stdout and stderr are printed instead of
        being collected.
    '''
    if workspace is None:
      workspace = self.workflow_workspace
    control_uri_cmd_line = '-c %s' % control_uri if control_uri is not None else ''
    param_cmd_line = ' '.join('--param "%s=%s"' % (k,v) for k,v in params.iteritems())
    extensions_cmd_line = ' '.join('--extension %s' % x for x in extensions)
    commands = ['lb web-services load-services -w %s' % ' '.join(self.workspaces.values())] if load_services else []
    commands.extend([
      'lb workflow install -f %s --workspace %s --name %s --main %s %s %s' % (filename, workspace, name, main, param_cmd_line, extensions_cmd_line),
      'lb workflow start --name %s %s' % (name, control_uri_cmd_line),
      'lb workflow driver --auto-terminate 1 --workspace %s %s' % (workspace, extensions_cmd_line)
    ])
    # in debug mode, use subprocess.check_call, which immediately prints to stdout
    for command in commands:
      if debug:
        print command
        ret = (subprocess.check_call(command, shell=True), None, None)
      else:
        ret = self.check_call(command)

    return ret


  def lb_workflow_install(self, filename, main='main', name='/default', params={},
    workspace=None, extensions=[]):
    if workspace is None:
      workspace = self.workflow_workspace
    param_cmd_line = ' '.join('--param "%s=%s"' % (k,v) for k,v in params.iteritems())
    extensions_cmd_line = ' '.join('--extension %s' % x for x in extensions)
    command = 'lb workflow install -f %s --workspace %s --name %s --main %s %s %s' % (filename, workspace, name, main, param_cmd_line, extensions_cmd_line),
    return self.check_call(command)


  def lb_workflow_start(self, name=None, control_uri=None, params=[],
    workspace=None):
    '''Start an lb workflow.

      @param control_uri
        The URI of the control service to use (currently for starting the workflow).

      @param params A list of strings to be appended as parameters to the main workflow. Each entry should have the
      format 'parameter=value'.

      @return a tuple (retcode, stdout, stderr) with the return code, standard
        output printout and standard error printout for the process created to
        start the workflow.
    '''
    if name is None:
      name = '/default'
    command = 'lb workflow start --name %s ' % name
    if control_uri is not None:
      command += '-c %s ' % control_uri
    for param in params:
      command += ' --param %s' % param
    return self.check_call(command)


  def lb_workflow_drive(self, workspace=None):
    '''Execute the lb workflow driver.

      @return a tuple (retcode, stdout, stderr) with the return code, standard
        output printout and standard error printout for the process created to
        start the workflow.
    '''
    if workspace is None:
      workspace = self.workflow_workspace
    command = 'lb workflow driver --auto-terminate 1 --workspace %s' % workspace
    return self.check_call(command)
