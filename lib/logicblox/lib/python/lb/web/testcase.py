import copy
import lb.web.admin
import dbcommands.lb_command
import blox.connect.relations
import service
import subprocess
import types
import tempfile
import uuid

from google.protobuf import text_format

try:
    import unittest2 as unittest
except ImportError:
    import unittest


class CallError(Exception):
    '''An exception similar to subprocess.CalledProcessError but which also dumps the
    standard output and error when printed. 
    '''
    def __init__(self, retcode, command, out, err):
        self.retcode = retcode
        self.command = command
        self.out = out
        self.err = err

    def __str__(self):
        return "Command '%s' returned non-zero exit status %d:\n\nStdOut:\n%s\n\nStdError:\n%s" % (self.command, self.retcode, self.out, self.err)



class TestCase(unittest.TestCase):
    '''A class to facilitate testing of lb-web services.

    This class contains helper methods to support test implementation. Consider using sub-types
    like MultiplePrototypeWorkspacesTestCase or PrototypeWorkspaceTestCase because they provide
    support or branching workspace on each test case.
    '''

    def call_output(self, command):
        '''Execute the command as an external process and wait for its completion. 

        @param command
          The full command line to execute, as a string.

        @return a tuple (return_code, standard_output, standard_error)
        '''
        process = subprocess.Popen(command, shell = True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stderr = process.communicate()
        return process.wait(), stdout, stderr

    def check_call(self, command):
        '''Execute the command as an external process, wait for its completion and raise an error if
        the external program failed.

        @param command
          The full command line to execute, as a string.

        @return a tuple (return_code, standard_output, standard_error)
        '''
        retcode, out, err = self.call_output(command)
        if retcode:      
            raise CallError(retcode, command, out, err)
        return (retcode, out, err)


    def assertMessageEqual(self, msg1, msg2):
        '''Assert equality of two protobuf messages.

        @param msg1
		A protobuf message or a dict representation
                of a protobuf message. If msg1 is a dict,
                we convert msg2 into dict and compare.
        @param msg2 
		A protobuf message.
        '''
        if isinstance(msg1, dict):
            msg2 = lb.web.protobuf_json.protobuf_to_dict(msg2)
        if isinstance(msg2, basestring):
            notext_msg2 = copy.copy(msg1)
            notext_msg2.Clear()
            text_format.Merge(msg2, notext_msg2)
            self.assertEqual(msg1, notext_msg2)
        else:
            self.assertEqual(msg1, msg2)

    def assertDelimEqual(self, delim1, delim2):
        '''Assert equality of the content of two delimited files.

        @param delim1
		A DelimitedFile object or a string with the
                content of a delimited file;
        @param delim2
		A DelimitedFile object or a string with the
                content of a delimited file.
        '''

        if not isinstance(delim1, service.DelimitedFile):
            set1 = set(map(tuple, service.DelimitedFile.from_dynamic(delim1).cells()))
        else:
            set1 = set(map(tuple, delim1.cells()))

        if not isinstance(delim2, service.DelimitedFile):
            set2 = set(map(tuple, service.DelimitedFile.from_dynamic(delim2).cells()))
        else:
            set2 = set(map(tuple, delim2.cells()))

        self.assertEqual(set1, set2)

    def assertHasField(self, msg, fieldname):
        '''Assert that a protobuf message has a field.

        @param msg
		A protobuf message.
        @param fieldname
		The name of the field to check for.
        '''
        self.assertTrue(msg.HasField(fieldname))

    def assertNotHasField(self, msg, fieldname):
        '''Assert that a protobuf message does not have a field.

        @param msg
		A protobuf message.
        @param fieldname
		The name of the field to check for.
        '''
        self.assertFalse(msg.HasField(fieldname))

    def assertMessageUnorderedEqual(self, l1, l2):
        """Assert that two lists of protobuf message have the same elements.

        Compares two lists of protobuf messages and asserts that they
        are equal, where order is considered irrelevant.
        @param l1
		A list of protobuf messages.
        @param l2
		A list of protobuf messages.
        """
        s1 = [text_format.MessageToString(m) for m in l1]
        s2 = [text_format.MessageToString(m) for m in l2]
        self.assertUnorderedEqual(s1, s2)

    def printMessage(self, msg):
        '''Convert and print a protobuf message to readable format.

        @param msg
		Message to print.'''
        print "---------------------------------------- "
        print self.messageToString(msg)
        print "---------------------------------------- "

    def messageToString(self, msg):
        '''Convert a protobuf message to reable format.

        @param msg
		Message to be converted.
        @return 
		A string representation of the message.'''
        return text_format.MessageToString(msg)

    def assertMessageStringEqual(self, msg1, msg2):
        '''Assert equality of string representation of two protobuf message.

        @param msg1
		A protobuf message.
        @param msg2
		A protobuf message.'''
        self.assertEqual(self.messageToString(msg1), self.messageToString(msg2))

    def assertUnorderedEqual(self, l1, l2):
        """Assert that two lists of protobuf messages have the same elements.

        Compares two lists of objects and asserts that they are equal,
        where order is considered irrelevant.

        First list can be a list of dictionaries representing protobuf_json
        versions of protobuf messages.
        @param l1: A list of protobuf messages or a list of dicts representing protobuf messages.
        @param l2: A list of protobuf messages.
        """
        self.assertEqual(len(l1), len(l2))
        for item in l1:
            try:
                item = lb.web.protobuf_json.protobuf_to_dict(item)
            except:
                pass
            self.assertTrue(item in l2, '%s is not in %s' % (str(item), str(l2)))

    def lb_exec(self, ws, logic):
        """Execute given logic, returning nothing.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param ws: Workspace in which to execute
        @param logic: Update to execute
        @return the result of the connectblox command
        """
        cmd = dbcommands.lb_command.ExecuteLogicCommand(workspace = ws, escape = False, logic = logic, should_print = False)
        result = cmd.run()
        return result

    def lb_exec_block(self, ws, block):
        """Execute given inactive block, returning nothing.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param ws: Workspace in which to execute
        @param block: Inactive block to execute
        @return the result of the connectblox command
        """
        cmd = dbcommands.lb_command.ExecuteBlockCommand(workspace = ws, escape = False, name = block, should_print = False)
        result = cmd.run()
        return result

    def lb_add_block(self, ws, name, logic):
        """Execute given inactive block, returning nothing.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param ws: Workspace in which to execute
        @param block: Inactive block to execute
        @return the result of the connectblox command
        """
        cmd = dbcommands.lb_command.AddBlockCommand(name, ws, logic = logic)
        result = cmd.run()
        return result

    def lb_query(self, ws, logic):
        """Return a list of tuples (facts) for the given query.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param ws: Workspace in which to execute.
        @param logic: Query to execute.
        @return: list of facts.
        """
        cmd = dbcommands.lb_command.ExecuteLogicCommand(workspace = ws, escape = False, logic = logic, should_print = [[]])
        result = cmd.run()
        rel_objects = []
        for rel in result.output_relations:
            rel_objects.append(rel[1])

        rels = blox.connect.relations.Relations(rel_objects)
        return rels.get_values(result.output_relations[0][1].name)

    def create_branch(self, workspace_name, branch_name, parent = None):
        '''Create a new branch in the workspace, with this branch_name.'''
        cmd = dbcommands.lb_command.CreateBranchCommand(workspace_name, branch_name, parent)
        cmd.run()

    def list_branch(self, workspace_name, parent = None):
        '''Lists the branches in the workspace with this workspace_name.'''
        cmd = dbcommands.lb_command.ListBranchesCommand(workspace_name, False)
        result = cmd.run()
        return result

    def delete_branch(self, workspace_name, branch_name):
        '''Delete the branch with this branch_name in the workspace with this workspace_name.'''
        cmd = dbcommands.lb_command.DeleteBranchCommand(workspace_name, branch_name)
        cmd.run()


class WorkspaceTestCase(TestCase):
    '''A utility class that starts up and shutsdown workspaces

    This is important so that tests are isolated and a service started
    by one test doesn't affect other tests.'''

    def setUp(self):
        super(WorkspaceTestCase, self).setUp()
        admin_client = lb.web.admin.Client()
        admin_client.start_exclusive_service_set(self.workspaces)

    def tearDown(self):
        super(WorkspaceTestCase, self).tearDown()
        admin_client = lb.web.admin.Client()
        admin_client.stop_service(self.workspaces)



class MultiplePrototypeWorkspacesTestCase(TestCase):
    '''A utility class for testing bloxweb services that work with several workspaces.

    Subtypes should declare an attribute called "prototypes" with an array
    of strings. When a test is setup, each workspace declared in prototypes 
    will be branched; self.workspace_branch may be used to define the name
    of the branch; self.workspaces will be a map from prototype to
    the full name to address the branch (i.e. $prototype@$branch).

    If delete_branches_on_tear_down is set to True, the test will delete branches
    on tear down.
    '''
    #
    # Class Level Members
    #

    # reusable client to the admin service
    admin_client = lb.web.admin.Client();

    # Sub-types must define the prototypes, which is a list with the name of the workspaces 
    # that will be branched for each test case.
    prototypes = []

    # Whether branches created for testcases should be deleted when tearing down
    delete_branches_on_tear_down = True

    # If true, stop services on the master branch before running tests, and reload afterwards
    maintain_master_branch_services = False

    # If true, only services in the prototype workspace will be active
    exclusive_service_set = True

    @classmethod
    def setUpClass(cls):
        super(MultiplePrototypeWorkspacesTestCase, cls).setUpClass()        
        # stop services running on master branches
        if cls.maintain_master_branch_services:
            cls.admin_client.stop_service(cls.prototypes)

    @classmethod
    def tearDownClass(cls):
        super(MultiplePrototypeWorkspacesTestCase, cls).tearDownClass()
        # restart services on master branches
        if cls.maintain_master_branch_services:
            cls.admin_client.start_service(cls.prototypes)

    #
    # Instance Level Members
    #

    # Sub-types may define the prefix of the branches to create. If undefined, the branches will bee named
    # after the test class and method, followed by a unique identifier.
    workspace_branch = None

    # SetUp will fill this with a map from the prototype name (from prototypes) to the full name of the branch 
    # being used by the test (prototype@branch).
    workspaces = dict()

    # Branch names only
    branches = dict()

    def setUp(self):
        '''Create branches on all workspaces in self.prototypes, and start services on them.'''
        
        # either use a client-define branch name, or use the test id (usually the class and method name,
        # minus "__main__." plus a generated uuid)
        if self.workspace_branch is None:
            self.workspace_branch = self.id()[9:] + "_" + str(uuid.uuid4())
            self.workspace_branch = self.workspace_branch.replace('.', '_').replace('-', '_')

        # create a branch on each prototype and record the created branch in workspaces
        self.workspaces = dict()
        for prototype in self.prototypes:
            ## delete leftover branches if the exist
            existingBranches = self.list_branch(prototype)
            if self.workspace_branch in existingBranches.names:
                self.delete_branch(prototype, self.workspace_branch)
            
            self.create_branch(prototype, self.workspace_branch)

            self.workspaces[prototype] = prototype + '@' + self.workspace_branch
            self.branches[prototype] = self.workspace_branch

        if self.exclusive_service_set:
            # ensure only the branches have services hosted
            self.admin_client.start_exclusive_service_set(self.workspaces.values())
        else:
            self.admin_client.start_service(self.workspaces.values())


    def tearDown(self):
        '''Stop services and delete branches created on setup.'''
        if self.delete_branches_on_tear_down:
            for prototype in self.prototypes:
                self.delete_branch(prototype, self.workspace_branch)

        self.admin_client.stop_service(self.workspaces.values())
        self.workspaces = dict()
        self.branches = dict()


class PrototypeWorkspaceTestCase(MultiplePrototypeWorkspacesTestCase):
    '''A specialization of MultiplePrototypeWorkspacesTestCase for a single workspace.'''
    #
    # Class Level Members
    #

    # Sub-types must define the prototype, which is the name of the workspace that will be branched
    # for each test case.
    prototype = None

    @classmethod
    def setUpClass(cls):
        cls.prototypes = [cls.prototype]
        super(PrototypeWorkspaceTestCase, cls).setUpClass()

    #
    # Instance Level Members
    #

    # SetUp will fill this with the full name of the branch being used by the test (prototype@branch).
    workspace = None

    # Branch name only
    branch = None

    def setUp(self):
        '''Create a new branch and start the services in that branch.'''
        super(PrototypeWorkspaceTestCase, self).setUp()
        self.workspace = self.workspaces[self.prototype]
        self.branch = self.branches[self.prototype]

    def tearDown(self):
        '''Revert back to master.'''
        super(PrototypeWorkspaceTestCase, self).tearDown()
        workspace = None

    def ws_exec(self, logic):
        """Execute given logic in the cloned workspace, returning nothing.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param logic Update to execute.
        """
        return self.lb_exec(self.workspace, logic)

    def ws_query(self, logic):
        """Return a list of tuples (facts) for the given query in the cloned workspace.

        Caution: this command will only work locally, because it uses
        ConnectBlox directly.

        @param logic Query to execute.
        """
        return self.lb_query(self.workspace, logic)

