import lb.web.testcase
import dbcommands.lb_command

class WorkbooksTestCase(lb.web.testcase.PrototypeWorkspaceTestCase):

    
    def setUp(self):
        super(WorkbooksTestCase, self).setUp()
        self.branches = []

    def tearDown(self):
        super(WorkbooksTestCase, self).tearDown()
        for id in self.branches:
            #print "deleting %s"%id
            try:
                dbcommands.lb_command.DeleteBranchCommand(workspace=self.workspace.split('@')[0], name = str(id)).run()
            except Exception as e:
                pass

    def register(self,id):
        self.branches.append(id)
