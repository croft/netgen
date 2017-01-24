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

import blox.connect.ConnectBlox_pb2
from blox.connect.BloxCommand_pb2 import ASSERTIONS
from blox.connect.BloxCommand_pb2 import RETRACTIONS
from blox.common.Common_pb2 import ACTIVE
from google.protobuf import text_format
from google.protobuf.message import Message
import os, tempfile, shutil, sys, hashlib, time, uuid, signal

import blox.connect.io
from cli import lb_exception
from cli import util



# debug mode can be set with an environment variable
LB_DEBUG='LB_DEBUG' in os.environ


class LBCommandResult(object):
    '''
        Represents the result of a command, extracted from a connect blox response.
    '''
    @classmethod
    def from_response(class_, response, lbcommand, bloxcommand_response=None):
        '''
            @param response the connectblox response

            @param lbcommand the LBCommand object that originated the request that eventually caused
                             this connectlbox response from the server

            @return an instance of this class, configured with this response to this command.

            @param bloxcommand_response the bloxcommand object inside the response that corresponds
                                        to the lbcommand, if any.
        '''
        return class_(response, lbcommand, bloxcommand_response)


    def __init__(self, response, lbcommand, bloxcommand_response=None):
        '''
            Constructs a command result.

            @param response the connectblox response

            @param lbcommand the LBCommand object that originated the request that eventually caused
                             this connectlbox response from the server

            @param bloxcommand_response the bloxcommand object inside the response that corresponds
                                        to the lbcommand, if any.
        '''

        # if available, store the log
        if hasattr(response, "compressed_log"):
            self.log = response.compressed_log

        # initialize a list of output relations
        self.output_relations = []

        # yes, even if we do not monitor results, we still initialize this array
        self.monitor_results = []
        if lbcommand.monitor != None:
            # here we assume that when we monitor results, everything after fixpoint is the
            # result of monitoring. This is clearly wrong and will break at some point.
            i = 0
            for pred in lbcommand.monitor:
                assertions = response.transaction.command_after_fixpoint[i].query_predicate.relation
                i = i + 1
                retractions = response.transaction.command_after_fixpoint[i].query_predicate.relation
                i = i + 1
                self.monitor_results.append((pred, (assertions, retractions)))



class LBAdminCommandResult(LBCommandResult):
    '''
        The result of an admin command.
    '''
    def __init__(self, response, lbcommand, bloxcommand_response=None):
        self.log = None
        self.output_relations = []
        self.should_monitor = True if lbcommand.monitor is not None else False



class LBCommand(object):
    '''
        Represents a command that will be transformed into a connectblox request.
    '''

    FILE_OR_LOGIC_MSG = "Either file or logic must be specified!"
    LANG_MUST_BE_LOGIC_OR_LB0 = "Language must be 'lb' or 'lb0'"

    @classmethod
    def from_args(class_, conn, args, interactive=None):
        '''
            TODO - decypher what we are actually doing here.
        '''
        arg_dict = vars(args)
        if 'func' in arg_dict:
            del arg_dict['func']
        if 'print' in arg_dict:
            arg_dict['should_print'] = arg_dict['print']
            del arg_dict['print']
        if interactive:
            arg_dict['cwd'] = interactive.current_directory
            if not 'workspace' in arg_dict:
                arg_dict['workspace'] = interactive.current_workspace
            if arg_dict.get('loglevel', None) is None and getattr(interactive, 'loglevel', None) is not None:
                arg_dict['loglevel'] = interactive.loglevel
                arg_dict['log'] = True
        if 'commit_mode' not in arg_dict:
            arg_dict['commit_mode'] = None
        # set current working directory

        lbcommand = class_(conn=conn, **arg_dict)

        # Check if a command run in an interactive session has a nonempty workspace argument
        if interactive and hasattr(lbcommand, 'workspace') and not lbcommand.workspace:
            raise lb_exception.LBCommandError("No open workspace. Use command 'workspaces' for an existing list of workspaces")

        return lbcommand


    def __init__(self, conn=None, log=False, loglevel=None, monitor=None,
            priority=None, isAdmin=False, serialize_requests=False, cwd=None, timeout=None,
            exclusive=None, readonly=None, commit_mode=None, branch=None, **kw):
        '''
            @param conn an optional connectblox connection to use (an object of type blox.connect.io.Connection).
                        The connection must be open already. If no connection is given, this constructor will create one.

            @param log

            @param loglevel

            @param monitor a list of names of predicates that should be monitored during the execution of this command.

            @param priority

            @param isAdmin whether this is an admin command (see LBAdminCommand class)

            @param serialize_requests whether all requests to the server should be synchronous, i.e., if we should
                                      ensure that only one request is being executed at a time (in this python process).

            @param cwd

            @param timeout if this is a transaction, the timeout in milliseconds

            @param exclusive if this is a transaction, whether it should run exclusivelly in the runtime

            @param readonly if this is a transaction, whether it is readonly

            @param commit_mode if this is a transaction, its commit mode, which specifies (when the response for the
                               transaction is sent back to the client). This can be 'softcommit' (transaction has
                               finished and been committed to memory),'diskcommit' (transaction has been fully
                               committed to local disk) or None (use the server default)

            @param kw whatever you want to pass to this constructor...

        '''
        if conn is None:
            admin = isAdmin if isAdmin is not None else False
            conn = blox.connect.io.Connection(admin)
            conn.open()
        self.conn = conn
        self.log = log
        self.loglevel = loglevel
        self.monitor = monitor
        self.priority = priority
        self.serialize_requests = serialize_requests
        self.cwd = cwd
        self.timeout = timeout
        self.guid = str(uuid.uuid1())
        self.exclusive = exclusive
        self.readonly = readonly
        self.commit_mode = commit_mode
        self.branch = branch

        # always keep the correspondence between this lbcommand and the blox command object
        # that was created for it in a transaction. Only set when decorating the command and when
        # the lbcommand corresponds to a blox command inside a connectblox transaction.
        self.blox_command = None


    def run(self):
        '''
            Execute this command, creating a connectblox request, sending to the server
            and encapsulating the response into an LBCommandResult.

            @return the LBCommandResult object created from the connectblox response.
        '''
        # the default command just pings the server
        request = self._create_request()
        self._decorate_request(request)
        response = self._send_request(request)
        bloxcommand_response = None
        if hasattr(response, 'transaction') and response.transaction.command:
            bloxcommand_response = response.transaction.command[0]
        return self.result_class.from_response(response, self, bloxcommand_response)

    @property
    def result_class(self):
        '''
            @return the class that should encapsulate the connectblox response for this command.
        '''
        # by default, strip off Command from this class and add Result to
        # find the result classname
        this_class_prefix = self.__class__.__name__[:-7]
        result_class_name = '%sResult' % this_class_prefix

        this_module = sys.modules[self.__class__.__module__]
        result_class_ = getattr(this_module, result_class_name)
        return result_class_

    @property
    def request_class(self):
        '''
            @return the class to construct connectblox requests for this command.
        '''
        return blox.connect.ConnectBlox_pb2.Request


    def initialize_transaction(self, request, workspace):
        '''
            Initializes the transaction object of this request with the values stored in
            self. See __init__ for a description of transaction properties.
        '''
        #commented out until timeout are supported by lb-server
#        if self.timeout is not None:
#            request.transaction.timeout = self.timeout
        if self.exclusive is not None:
            request.transaction.exclusive = self.exclusive
        if self.readonly is not None:
            request.transaction.readonly = self.readonly
        if self.commit_mode is not None:
            request.transaction.commit_mode = self.commit_mode
        if self.branch is not None:
            request.transaction.workspace = '%s@%s' % (workspace, self.branch)
        else:
            request.transaction.workspace = workspace

    def _create_request(self):
        '''
            @return a new request object (of type request_class()) configured according to
                    this command.
        '''
        # create using the specific request class for this command
        request = self.request_class()

        # set some default values for it
        if self.loglevel is not None:
            request.log_level = self.loglevel
        if self.log is True:
            request.return_log = True
        if self.cwd is not None:
            request.current_working_directory = os.path.abspath(self.cwd)

        # potentially add monitoring commands
        self._add_monitor_commands(request)

        # add GUID to the request so we pass it to lb-server
        request.guid = self.guid

        return request


    def _add_monitor_commands(self, request):
        '''
            If this command was configured with monitoring, this function will add
            commands to the request to execute the monitoring.
        '''
        if isinstance(self.monitor, list):
            for predicate_name in self.monitor:

                # monitor assertions into a predicate
                cmd = request.transaction.command_after_fixpoint.add()
                cmd.query_predicate.delta = ASSERTIONS
                cmd.query_predicate.predicate.global_name.qualified_name = predicate_name

                # monitor retractions from a predicate
                cmd = request.transaction.command_after_fixpoint.add()
                cmd.query_predicate.delta = RETRACTIONS
                cmd.query_predicate.predicate.global_name.qualified_name = predicate_name


    def _decorate_request(self, request):
        '''
            A template method for sub-types to enrich the request after it's been created
            but before sending it to the connectblox server. The default implementation
            does nothing.

            @param request the connectblox protobuf request object being created for this command.
        '''
        pass


    def _decorate_transaction_request(self, blox_command, request):
        '''
            A template method for sub-types to enrich the blox_command when this command
            is going to be executed inside a transaction. The default implementation
            does nothing.

            @param blox_command the bloxcommand protobuf object corresponding to this lb command.

            @param request the connectblox protobuf request object being created for the whole
                           transaction.
        '''
        pass


    def _send_request(self, request, ignore_exception=False):
        '''
            Send the request to the connectblox server.

            @param request the request to be sent (of type request_class())

            @param ignore_exception whether exceptions included in the connectblox response
                                    should be ignored. If False, this function will raise an
                                    exception with the contents of the connectblox exception.
                                    Otherwise, the response will be returned even if it contains
                                    an exception.

            @return the response object returned from the connectblox server.
        '''
        # at debug mode, print the request
        if LB_DEBUG:
            print('LB_DEBUG: connectblox request =\n' + text_format.MessageToString(request))


        # setting an alarm if there is a timeout
        if self.timeout is not None and self.timeout>0:
            util.set_alarm_handler(self.timeout)
            # rounds up to the second
            signal.alarm((self.timeout+999)/1000)

        #setting the guid to enable cleanup in case of interruption
        util.current_guid = self.guid

        # if we should serialize requests, acquire a lock first
        if self.serialize_requests:
            with self._backend_lock:
                response = self.conn.call(request)
        else:
            response = self.conn.call(request)

            # ad debug mode, print the response
            if LB_DEBUG:
                print('LB_DEBUG: connectblox response =\n' + text_format.MessageToString(response))

        #nothing to interrupt when the call has returned
        util.current_guid = None
        signal.alarm(0)

        # deal with exceptions in the response
        if not ignore_exception:
            if response.HasField("exception"):
                msg = response.exception.message
                if msg.startswith('ERROR '):
                    msg = msg[6:]
                raise lb_exception.LBCommandError(msg)
        return response


    def _workspace_exists(self, name):
        '''
            TODO - remove this method, it makes no sense here.

            @return whether a workspace with this name exists.
        '''
        cmd = WorkspaceExistsCommand(name, conn = self.conn, log = self.log,
                loglevel = self.loglevel, monitor = self.monitor,
                priority = self.priority, isAdmin = False, serialize_requests = self.serialize_requests)
        result = cmd.run()
        return result.exists

    def _decorate_with_authenticator(self, workspaceName, req):
        """A helper function that adds an authentication token to the request.
        Use this when sending workspace delete requests."""

        # we only need to add an authenticator if the request goes through a regular tcp
        # connection (indicated by having a port). If a unix socket is used, then that is
        # not necessary.
        if hasattr(self.conn, "port"):
            port = self.conn.port
            secret_file = "%s/.lb-server.%s.secret" % (util.get_lb_deployment_home(), port)

            if os.path.isfile(secret_file):
                try:
                    with open(secret_file, 'r') as f:
                        secret = f.read()
                    t = time.strftime('%s')
                    token = "::%s::%s::%s::" % (t, str(workspaceName), secret)
                    req.authenticator = t + "::" + hashlib.sha512(token).hexdigest()
                except IOError:
                    print "Could not read authentication secret from file %s" % secret_file


class LBAdminCommand(LBCommand):
    '''
        An LBCommand specific for admin commands.
    '''
    def __init__(self, conn=None, log=False, loglevel=None, monitor=None,
            priority=None, isAdmin=True, serialize_requests=False, **kw):
        super(LBAdminCommand, self).__init__(
            conn=conn,log=log,loglevel=loglevel,monitor=monitor,
            priority=priority,isAdmin=isAdmin,serialize_requests=serialize_requests,
            **kw)

    @property
    def request_class(self):
        # an admin command must be encapsulated in a different class than a regular
        # command, so we override this method to return the proper class
        return blox.connect.ConnectBlox_pb2.AdminRequest

    def _create_request(self):
        # overwrite method in LBAdminCommand to avoid setting the loglevel and cwd

        # create using the specific request class for this command
        request = self.request_class()

        # Note: Admin requests do not support return_log
        # if self.log is True:
        #     request.return_log = True

        #if self.cwd is not None:
        #    request.current_working_directory = os.path.abspath(self.cwd)

        # potentially add monitoring commands
        self._add_monitor_commands(request)
        return request





class TransactionResult(LBCommandResult):
    '''
        An object to encapsulate the response of a transaction request.
    '''

    def __init__(self, response, lbcommand, bloxcommand_response):
        super(TransactionResult,self).__init__(response, lbcommand, bloxcommand_response)

        # mapping of response objects from protocol buffer to command result classes
        response_to_result_dict = {
            "AddBlockResponse":"AddBlockResult",
            "InstallLibraryResponse":"AddLibraryResult",
            "ExecInactiveBlockResponse":"ExecuteBlockResult",
            "ExecBlockResponse":"ExecuteLogicResult",
            "QueryPredicateResponse":"PrintPredicateResult",
            "UpdatePredicateResponse":None,
            "GetPredicateInfoResponse":"PredicateInfoResult",
            "GetPredicateInfoBulkResponse":None,
            "ImportProtoBufResponse":"ImportProtobufResult",
            "CompileBlockResponse":"CompileBlockResult",
            "InstallProjectResponse":"AddProjectResult",
            "RemoveBlockResponse":"RemoveBlockResult",
            "LogMessageResponse":"InsertLogMessageResult",
            "ReplaceBlockResponse":"ReplaceBlockResult",
            "ExportProtoBufResponse":"ExportProtobufResult",
            "ProtoAddSpecResponse":"ProtoAddSpecResult",
            "FaultInjection":None,
            "XMLAddSpecResponse":"XMLAddSpecResult",
            "ImportXMLDocResponse":"ImportXMLResult",
            "GetPredicatePopcountResponse":"PredicatePopcountResult",
            "GetProtocolDescriptorsResponse": "GetProtocolDescriptorsResult"
        }

        # decorate command response of each transaction command
        def parse_transaction_command_response(request_lbcommands, response_transaction_command, lbcommand_result_list):
            '''

            '''
            for i, bloxcommand_response in enumerate(response_transaction_command):
                descriptor, r = bloxcommand_response.ListFields()[0]
                result_class_name = response_to_result_dict[r.__class__.__name__]
                result_class = getattr(sys.modules[__name__], result_class_name)
                lbcommand_result_object = result_class(response, request_lbcommands[i], bloxcommand_response)
                lbcommand_result_object.name = descriptor.name

                lbcommand_result_list.append(lbcommand_result_object)


        # transaction commands before fix point
        self.transaction_cmds = []
        parse_transaction_command_response(lbcommand.commands, response.transaction.command, self.transaction_cmds)

        # transaction commands after fix point
        self.transaction_cmds_after_fixpoint = []
        parse_transaction_command_response(lbcommand.commands_after_fixpoint, response.transaction.command_after_fixpoint, self.transaction_cmds_after_fixpoint)



class TransactionCommand(LBCommand):
    '''
        An LBCommand that represents a transaction with multiple commands.
    '''

    def __init__(self, workspace, commands, commands_after_fixpoint, **kw):
        '''
            Initialize this transaction command.

            @param workspace

            @param commands a list of Namespaces that represent commands parsed from the command line. These are the
                            objects returned by argparser after it parsed a command line. See lb_argparser. These are
                            *not* LBCommand objects.

            @param commands_after_fixpoint a list with the same type of objects as the "commands" parameter, but with
                                           commands that should be executed after fixpoint.

            @param kw yey!
        '''
        super(TransactionCommand, self).__init__(**kw)

        # set attributes that are specific to transactions
        self.workspace = workspace
        self.cmdline_commands = commands
        self.cmdline_commands_after_fixpoint = commands_after_fixpoint


    def _decorate_request(self, request):
        '''
            Override to fill the request with commands.
        '''
        # set basic properties of the request
        self.initialize_transaction(request, self.workspace)

        def build_lb_command(cmdline_command, blox_command):
            '''
                Build an LBCommand object from information in the cmdline_command. Also decorate
                the blox_command object with information extracted from the built LBCommand.

                @return the LBCommand that was instantiated.
            '''
            cmdline_command.workspace = self.workspace

            # initialize the command from the cmdline. The class object is taked from the name in the cmd attribute of
            # the cmdline_command.
            lbcommand = getattr(sys.modules[__name__], "%sCommand" % vars(cmdline_command)['cmd']).from_args(None, cmdline_command)

            # make sure we keep the correspondence between lbcommand object and the blox_command protobuf object representing it
            lbcommand.blox_command = blox_command

            # decorate the protobuf command with information from the command
            lbcommand._decorate_transaction_request(blox_command, request)
            return lbcommand

        # build commands from cmdline_commands
        self.commands = []
        for cmdline_command in self.cmdline_commands:
            self.commands.append(build_lb_command(cmdline_command, request.transaction.command.add()))

        # build commands_after_fixpoint from cmdline_commands_after_fixpoint
        self.commands_after_fixpoint = []
        for cmdline_command in self.cmdline_commands_after_fixpoint:
            self.commands_after_fixpoint.append(build_lb_command(cmdline_command, request.transaction.command_after_fixpoint.add()))


    def run(self):
        '''
            TODO - is this useless?
        '''
        return super(TransactionCommand, self).run()




class CreateWorkspaceResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(CreateWorkspaceResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.workspace_name = response.create.name

class CreateWorkspaceCommand(LBCommand):
    def __init__(self, name, unique, overwrite, libs=None, **kw):
        """ Command to create a new workspace
        """
        super(CreateWorkspaceCommand, self).__init__(**kw)

        self.name = name
        self.unique = unique
        self.overwrite = overwrite
        self.libs = libs

    def run(self):
        return super(CreateWorkspaceCommand, self).run()

    def _decorate_request(self, req):
        super(CreateWorkspaceCommand,self)._decorate_request(req)
        if self.name:
           req.create.name = self.name
        if self.libs != None:
           req.create.libraries = self.libs
        req.create.overwrite = self.overwrite
        if self.overwrite:
            self._decorate_with_authenticator(self.name, req)

        req.create.unique = self.unique


class ExecuteBlockResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ExecuteBlockResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.return_local = lbcommand.return_local
        for name, rel in zip(self.return_local, bloxcommand_response.exec_inactive.return_local):
            self.output_relations.append((name, rel))

        # This is a bit of a hack in that the ExecuteBlockCommand sometimes needs 2 bloxcommand
        # commands. So here it tries to get the corresponding response by getting the position
        # of the bloxcommand_reponse for the first command in the transaction and getting the next
        # response object. The problem is that it uses the command list, and exec block could
        # perhaps be in command_after_fixpoint. The way to fix this is to have a better link
        # between requests and responses.
        has_msgCls = hasattr(lbcommand, "msgCls") and lbcommand.msgCls is not None
        if has_msgCls and issubclass(lbcommand.msgCls, Message):
            pos = response.transaction.command.index(bloxcommand_response)
            proto_lbcommand = response.transaction.command[pos+1]
            msgInstance = lbcommand.msgCls()
            msgInstance.ParseFromString(proto_lbcommand.export_protobuf.message)
            self.message = msgInstance

        self.should_escape = lbcommand.escape
        self.output_csv = lbcommand.output_csv
        self.delimiter = lbcommand.delimiter
        self.exclude_ids = lbcommand.exclude_ids


class ExecuteBlockCommand(LBCommand):
    def __init__(self, name, workspace, escape, should_print=False, return_local=None, **kw):
        self.name = name
        self.workspace = workspace
        self.escape = escape
        self.return_local = []
        if (should_print != None) and (isinstance(should_print, list)):
            # This is kind of ridiculous mess, but different versions
            # require different formats for should_print, so we check
            # for a bunch of different variants. Clearly, there should
            # just be a clear parameter with a list of predicate
            # names/
            for rel in should_print:
                if rel == None:
                    self.return_local.append("_")
                elif rel == []:
                    self.return_local.append("_")
                elif isinstance(rel, basestring):
                    self.return_local.append(rel)
                elif isinstance(rel, list):
                    for predname in rel:
                        self.return_local.append(predname)
        self.msgCls = kw.pop('msgCls', None)
        self.msgType = kw.pop('msgType', None)
        self.protocol = kw.pop('protocol', None)
        self.inputs = kw.pop('inputs',[])
        self.branch_bindings = kw.pop('branch_bindings',[])
        self.output_csv = kw.get('output_csv', False)
        self.delimiter = kw.get('delimiter', None)
        self.exclude_ids = kw.get('exclude_ids', False)
        super(ExecuteBlockCommand, self).__init__(**kw)

    def _decorate_request(self, request):
        self.initialize_transaction(request, self.workspace)
        self.bloxcommand = request.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, request)
        for binding in self.branch_bindings:
            binding_command = request.transaction.command.add()
            binding_command.bind_branch_alias.alias = binding.alias
            binding_command.bind_branch_alias.branch_name = binding.branch_name


    def _decorate_transaction_request(self, bloxcommand, request):
        bloxcommand.exec_inactive.block_name = self.name
        if len(self.inputs) > 0:
            bloxcommand.exec_inactive.input.extend(self.inputs)

        has_msgCls = self.msgCls is not None
        has_msgType = self.msgType is not None
        has_protocol = self.protocol is not None

        if has_msgCls and has_msgType and has_protocol:
            bloxcommand = request.transaction.command.add()
            bloxcommand.export_protobuf.protocol = self.protocol
            bloxcommand.export_protobuf.type_name = self.msgType
        self._add_return_local_commands(request, bloxcommand)

    def _add_return_local_commands(self, request, bloxcommand):
        if isinstance(self.return_local,list):
            for pred in self.return_local:
                bloxcommand.exec_inactive.return_local.append(pred)


class ExecuteLogicResult(LBCommandResult):

    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ExecuteLogicResult,self).__init__(response, lbcommand, bloxcommand_response)
        if hasattr(lbcommand, 'return_local'):
            self.return_local = lbcommand.return_local
        else:
            self.return_local = []

        for name, rel in zip(self.return_local, getattr(bloxcommand_response,'exec').return_local):
            self.output_relations.append((name, rel))

        self.should_escape = lbcommand.escape
        if isinstance(lbcommand.monitor,list):
            self.monitor_results = []
            i = 0
            for pred in lbcommand.monitor:
                rel1 = getattr(getattr(response.transaction.command_after_fixpoint[i], "query_predicate"),"relation")
                rel2 = getattr(getattr(response.transaction.command_after_fixpoint[i+1], "query_predicate"),"relation")
                self.monitor_results.append( (pred, (rel1, rel2)) );
                i = i + 2
        self.output_csv = lbcommand.output_csv
        self.delimiter = lbcommand.delimiter
        self.exclude_ids = lbcommand.exclude_ids
        if getattr(bloxcommand_response,'exec').problems is not None:
           self.errors = getattr(bloxcommand_response,'exec').problems


class ExecuteLogicCommand(LBCommand):
    def __init__(self, workspace, escape, blockname=None, language='lb', logic=None, should_print=False, file=None, block_name=None, **kw):
        if logic is None and file is None:
            raise lb_exception.LBCommandArgsError(LBCommand.FILE_OR_LOGIC_MSG)

        self.workspace = workspace
        if file is not None:
            logic = file.read()
        self.block_name = blockname
        self.language = blox.connect.BloxCommand_pb2.LB
        if language == 'lb':
            self.language = blox.connect.BloxCommand_pb2.LB
        elif language == 'lb0':
            self.language = blox.connect.BloxCommand_pb2.LB0
        else:
            raise lb_exception.LBCommandArgsError(LBCommand.LANG_MUST_BE_LOGIC_OR_LB0)

        self.logic = logic

        # only use block_name if blockname is None. I have no idea why there are 2 blockname parameters.
        if blockname is None:
            self.block_name = block_name

        self.branch_bindings = kw.pop('branch_bindings',[])
        self.return_local = []
        if (should_print != None) and (isinstance(should_print, list)):
            # This is kind of ridiculous mess, but different versions
            # require different formats for should_print, so we check
            # for a bunch of different variants. Clearly, there should
            # just be a clear parameter with a list of predicate
            # names/
            for rel in should_print:
                if rel == None:
                    self.return_local.append("_")
                elif rel == []:
                    self.return_local.append("_")
                elif isinstance(rel, basestring):
                    self.return_local.append(rel)
                elif isinstance(rel, list):
                    for predname in rel:
                        self.return_local.append(predname)

        self.escape = escape
        self.output_csv = kw.get('output_csv', False)
        self.delimiter = kw.get('delimiter', None)
        self.exclude_ids = kw.get('exclude_ids', False)
        super(ExecuteLogicCommand, self).__init__(**kw)

    def _decorate_request(self, request):
        self.initialize_transaction(request, self.workspace)
        self.blox_command = request.transaction.command.add()
        self._decorate_transaction_request(self.blox_command, request)
        for binding in self.branch_bindings:
            binding_command = request.transaction.command.add()
            binding_command.bind_branch_alias.alias = binding.alias
            binding_command.bind_branch_alias.branch_name = binding.branch_name

    def _decorate_transaction_request(self, blox_command, request):
        cmdexec = getattr(blox_command, 'exec')
        cmdexec.language = self.language
        cmdexec.logic = self.logic
        if self.block_name is not None:
            cmdexec.block_name = self.block_name
        self._add_return_local_commands(cmdexec)


    def _add_return_local_commands(self, cmdexec):
        if isinstance(self.return_local,list):
            for pred in self.return_local:
               cmdexec.return_local.append(pred)


# query is same as exec with --print option
class QueryLogicResult(ExecuteLogicResult):
    pass

class QueryLogicCommand(ExecuteLogicCommand):
    def __init__(self, workspace, escape, logic=None, file=None, should_print=['_'], **kw):
        if should_print is None:
            should_print = ['_']
        kw['readonly'] = True
        super(QueryLogicCommand, self).__init__(workspace, escape, logic=logic, should_print = should_print, file=file, **kw)


class DeleteWorkspaceResult(LBCommandResult): pass

class DeleteWorkspaceCommand(LBCommand):
    def __init__(self, name, force=False, **kw):
        super(DeleteWorkspaceCommand, self).__init__(**kw)
        self.name = name
        self.force = force

    def _decorate_request(self, req):
        req.delete.name = self.name
        if self.force:
            req.delete.ignore_nonexistent = True
        self._decorate_with_authenticator(self.name, req)


class WorkspaceFilepathResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(WorkspaceFilepathResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.filepath = response.get_ws_path.filepath

class WorkspaceFilepathCommand(LBCommand):
    def __init__(self, workspace, inverse=False, **kw):
        super(WorkspaceFilepathCommand, self).__init__(**kw)
        self.name = workspace
        self.inverse = inverse

    def _decorate_request(self, req):
        req.get_ws_path.name = self.name
        req.get_ws_path.inverse = self.inverse




class ListWorkspacesResult(LBAdminCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ListWorkspacesResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.names = [name for name in response.list_workspaces.name]

class ListWorkspacesCommand(LBAdminCommand):
    def __init__(self, **kw):
        super(ListWorkspacesCommand, self).__init__(**kw)

    def _decorate_request(self, req):
        req.list_workspaces = True

class CreateBranchResult(LBCommandResult): pass
class CreateBranchCommand(LBCommand):
    def __init__(self, workspace, name, parent, overwrite=False, **kw):
        super(CreateBranchCommand, self).__init__(**kw)
        self.workspace = workspace
        self.name = name
        self.parent = parent
        self.overwrite = overwrite

    def _decorate_request(self, req):
        req.create_named_branch.workspace = self.workspace
        req.create_named_branch.branch = self.name
        if self.parent is not None:
            req.create_named_branch.from_branch = self.parent
        req.create_named_branch.overwrite = self.overwrite

class DeleteBranchResult(LBCommandResult): pass
class DeleteBranchCommand(LBCommand):
    def __init__(self, workspace, name, **kw):
        super(DeleteBranchCommand, self).__init__(**kw)
        self.workspace = workspace
        self.name = name

    def _decorate_request(self, req):
        req.close_named_branch.workspace = self.workspace
        req.close_named_branch.branch = self.name

class DefaultBranchResult(LBCommandResult): pass
class DefaultBranchCommand(LBCommand):
    def __init__(self, workspace, name, **kw):
        super(DefaultBranchCommand, self).__init__(**kw)
        self.workspace = workspace
        self.name = name

    def _decorate_request(self, req):
        req.revert_database.workspace = self.workspace
        req.revert_database.older_branch = self.name
        self._decorate_with_authenticator(self.workspace, req)

class ListBranchesResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ListBranchesResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.names = [name for name in response.get_branch_names.names]

class ListBranchesCommand(LBCommand):
    def __init__(self, workspace, all, **kw):
        super(ListBranchesCommand, self).__init__(**kw)
        self.workspace = workspace
        self.all = all

    def _decorate_request(self, req):
        req.get_branch_names.workspace = self.workspace
        req.get_branch_names.include_auto_versions = self.all

class VersionResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(VersionResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.version = response.get_ws_version.version
        self.minor_version = response.get_ws_version.minor_version
        self.build_number = response.get_ws_version.build_number

class VersionCommand(LBCommand):
    def __init__(self, workspace, **kw):
        super(VersionCommand, self).__init__(**kw)
        if workspace == None:
            self.name = '/'
        else:
            self.name = workspace
    def _decorate_request(self, req):
        req.get_ws_version.name = self.name




class WorkspaceExistsResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        not_exists = (
            response.HasField('exception')
            and response.exception.HasField('message')
            and response.exception.message.startswith("Workspace '" + lbcommand.name + "' does not exist")
        )
        self.exists = not not_exists
        super(WorkspaceExistsResult,self).__init__(response, lbcommand)

class WorkspaceExistsCommand(LBCommand):
    def __init__(self, name, **kw):
        super(WorkspaceExistsCommand,self).__init__(**kw)
        self.name = name

    def run(self):
        req = self._create_request()
        self._decorate_request(req)
        # Ignore exception because that's what we use to know weather the ws exists or not
        res = self._send_request(req, True)
        return self.result_class.from_response(res, self)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.name)


class ExportWorkspaceResult(LBCommandResult): pass
class ExportWorkspaceCommand(LBCommand):
    def __init__(self, name, dest, overwrite=False, **kw):
        super(ExportWorkspaceCommand,self).__init__(**kw)
        self.name = name
        self.dest = dest
        self.overwrite = overwrite

    def _decorate_request(self, req):
        req.exportws.name = self.name
        req.exportws.dest_filepath = os.path.abspath(self.dest)
        req.exportws.overwrite = self.overwrite


class ImportWorkspaceResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ImportWorkspaceResult, self).__init__(response, lbcommand, bloxcommand_response)
        self.name = response.importws.name

class ImportWorkspaceCommand(LBCommand):
    def __init__(self, name, src, overwrite=False, unique=False, **kw):
        super(ImportWorkspaceCommand,self).__init__(**kw)
        self.name = name
        self.src = src
        self.overwrite = overwrite
        self.unique = unique

    def _decorate_request(self, req):
        if self.name is not None:
            req.importws.name = self.name
        req.importws.src_filepath = os.path.abspath(self.src)
        req.importws.overwrite = self.overwrite
        req.importws.unique = self.unique
        self._decorate_with_authenticator(self.name, req)


class PredicateInfoResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(PredicateInfoResult,self).__init__(response, lbcommand, bloxcommand_response)
        pred_info = bloxcommand_response.pred_info
        self.pred_info = text_format.MessageToString(pred_info)

class PredicateInfoCommand(LBCommand):
    def __init__(self, name, workspace, all, **kw):
        super(PredicateInfoCommand, self).__init__(**kw)
        self.name = name
        self.workspace = workspace

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        req.transaction.readonly = True
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.pred_info.predicate.global_name.qualified_name = self.name[0]



class PredicateInfoBulkResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(PredicateInfoBulkResult,self).__init__(response, lbcommand, bloxcommand_response)
        pred_info = bloxcommand_response.pred_info_bulk
        self.pred_info = text_format.MessageToString(pred_info)
        self.pred_info_message = pred_info

class PredicateInfoBulkCommand(LBCommand):
    def __init__(self, name, workspace, all, **kw):
        super(PredicateInfoBulkCommand, self).__init__(**kw)
        if all:
           self.all = True
        else:
           self.all = False
           self.requested_names = name

        self.workspace = workspace

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        # we here add and delete omit to create the pred_info_bulk container
        # to have a request even if self.requested_names is empty (indicating
        # that all user-predicates should be returned.
        self.bloxcommand.pred_info_bulk.omit.add()
        del self.bloxcommand.pred_info_bulk.omit[:]
        if not self.all:
           for pred_name in self.requested_names:
               reqname = self.bloxcommand.pred_info_bulk.predicate.add()
               reqname.global_name.qualified_name = pred_name



# NEEDS_WORK: unused - remove? ("lb list" uses PredicatePopcount.)
class ListPredicatesResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ListPredicatesResult,self).__init__(response, lbcommand, bloxcommand_response)
        rel = getattr(bloxcommand_response, 'exec').return_local[0]
        self.predicates_relation = rel

class ListPredicatesCommand(LBCommand):
    def __init__(self, workspace, **kw):
        super(ListPredicatesCommand,self).__init__(**kw)
        self.workspace = workspace

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        cmdexec = getattr(self.bloxcommand, 'exec')
        cmdexec.language = blox.connect.BloxCommand_pb2.LB
        cmdexec.logic = """
           _(name) <-
              system:Predicate:fullName[p] = name,
              !system:Predicate:displayName[p] = _.

           _(name) <-
              system:Predicate:displayName[_] = name.
        """
        cmdexec.return_local.append("_")



class PredicatePopcountResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(PredicatePopcountResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.pred_popcount = bloxcommand_response.pred_popcount

class PredicatePopcountCommand(LBCommand):
    def __init__(self, workspace, predicate, name=None, include=None,
            exclude=None, only_predicate_names=False, estimate=False,
            include_default=False, **kw):
        super(PredicatePopcountCommand, self).__init__(**kw)
        self.workspace = workspace
        self.predicate = predicate
        if (self.predicate is None) and (name is not None) and (len(name) > 0):
            self.predicate = []
        if name is not None:
            for n in name:
              self.predicate.append(n)
        self.include = include
        self.exclude = exclude
        self.only_predicate_names = only_predicate_names
        self.estimate = estimate
        self.include_default = include_default

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)
        req.transaction.readonly = True

    def _decorate_transaction_request(self, cmd, req):
        if self.only_predicate_names:
            cmd.pred_popcount.only_predicate_names = True

        if isinstance(self.predicate,list):
            cmd.pred_popcount.all = False
            for predname in self.predicate:
                pred = cmd.pred_popcount.predicate.add()
                pred.global_name.qualified_name = predname
        else:
            cmd.pred_popcount.all = True
            if self.include != None:
                cmd.pred_popcount.include_regexp = self.include
            if self.exclude != None:
                cmd.pred_popcount.exclude_regexp = self.exclude

        if self.estimate:
            cmd.pred_popcount.estimated = True

        if self.include_default:
            cmd.pred_popcount.include_default = True

# TODO - ListInactiveBlocks is currently not supported, so we use dlbatch scripts to list blocks
class ListInactiveBlocksResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ListInactiveBlocksResult,self).__init__(response, lbcommand, bloxcommand_response)
        rel = getattr(bloxcommand_response, 'exec').return_local[0]
        self.blocks_relation = rel

class ListInactiveBlocksCommand(LBCommand):
    def __init__(self, workspace, active=True, inactive=True, **kw):
        super(ListInactiveBlocksCommand,self).__init__(**kw)
        self.workspace = workspace
        self.active = active
        self.inactive = inactive

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        cmdexec = getattr(self.bloxcommand, 'exec')
        if self.inactive and not self.active:
           cmdexec.language = blox.connect.BloxCommand_pb2.LB
           cmdexec.logic = """
              _(name) <-
                 system:logic:logicBlockName[b] = name,
                 !system:logic:Block:displayName[b] = _,
                 !system:logic:ActiveBlock(b).

              _(displayName) <-
                 system:logic:Block:displayName[b] = displayName,
                 !system:logic:ActiveBlock(b).
           """
        else:
           if self.active and not self.inactive:
              cmdexec.logic += """
                 _(name) <-
                    system:logic:logicBlockName[b] = name,
                    !system:logic:Block:displayName[b] = _,
                    system:logic:ActiveBlock(b).

                 _(displayName) <-
                    system:logic:Block:displayName[b] = displayName,
                    system:logic:ActiveBlock(b).
              """
           else:
              cmdexec.logic += """
                 _(name) <-
                    system:logic:logicBlockName[b] = name,
                    !system:logic:Block:displayName[b] = _.

                 _(displayName) <-
                    system:logic:Block:displayName[b] = displayName.
              """
        cmdexec.return_local.append("_")





class PrintPredicateResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(PrintPredicateResult, self).__init__(response, lbcommand, bloxcommand_response)
        rel = bloxcommand_response.query_predicate.relation
        self.predicate_relation = rel
        self.should_escape = lbcommand.should_escape
        self.exclude_ids = lbcommand.exclude_ids

class PrintPredicateCommand(LBCommand):
    def __init__(self, name, workspace, should_escape=False, **kw):
        super(PrintPredicateCommand,self).__init__(**kw)
        self.name = name
        self.workspace = workspace
        self.should_escape = should_escape
        self.exclude_ids = kw.get('exclude_ids', False)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)
        req.transaction.readonly = True

    def _decorate_transaction_request(self, cmd, req):
        cmd.query_predicate.predicate.global_name.qualified_name = self.name



class AddBlockResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(AddBlockResult, self).__init__(response, lbcommand, bloxcommand_response)
        self.block_name = bloxcommand_response.add_block.block_name
        if bloxcommand_response.add_block.problems is not None:
            self.errors = bloxcommand_response.add_block.problems

class AddBlockCommand(LBCommand):
    def __init__(self, name, workspace, language='lb', logic=None, file=None, active=True, **kw):
        if logic is None and file is None:
            raise lb_exception.LBCommandArgsError(LBCommand.FILE_OR_LOGIC_MSG)
        self.workspace = workspace
        self.name = name
        if file is not None:
            logic = file.read()
            if self.name is None:
                file_basename = os.path.basename(file.name)
                self.name, ext = os.path.splitext(file_basename)
        self.language = blox.connect.BloxCommand_pb2.LB

        if language == 'lb':
            self.language = blox.connect.BloxCommand_pb2.LB
        elif language == 'lb0':
            self.language = blox.connect.BloxCommand_pb2.LB0
        else:
            raise lb_exception.LBCommandArgsError(LBCommand.LANG_MUST_BE_LOGIC_OR_LB0)

        self.logic = logic
        self.active = active
        super(AddBlockCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.add_block.language = self.language
        cmd.add_block.logic = self.logic
        if self.name is not None:
            cmd.add_block.block_name = self.name
        cmd.add_block.active = self.active



class CompileBlockResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(CompileBlockResult, self).__init__(response, lbcommand, bloxcommand_response)
        if bloxcommand_response.compile_block.problems is not None:
           self.errors = bloxcommand_response.compile_block.problems

class CompileBlockCommand(LBCommand):
    def __init__(self, name, workspace, logic=None, file=None, sort=ACTIVE, **kw):
        if logic is None and file is None:
            raise lb_exception.LBCommandArgsError(LBCommand.FILE_OR_LOGIC_MSG)
        self.workspace = workspace
        self.name = name
        if file is not None:
            logic = file.read()
            if self.name is None:
                file_basename = os.path.basename(file.name)
                self.name, ext = os.path.splitext(file_basename)
        self.language = blox.connect.BloxCommand_pb2.LB
        self.logic = logic
        self.sort = sort
        super(CompileBlockCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.compile_block.logic = self.logic
        if self.name is not None:
            cmd.compile_block.block_name = self.name
        cmd.compile_block.sort = self.sort



class ReplaceBlockResult(LBCommandResult): pass

class ReplaceBlockCommand(LBCommand):
    def __init__(self, blockname, workspace, logic, **kw):
        self.blockname = blockname
        self.workspace = workspace
        file_ = kw.pop('file', None)
        if file_ is not None:
            logic = file_.read()
        self.language = blox.connect.BloxCommand_pb2.LB
        self.logic = logic
        if file_ is None and logic is None:
            raise lb_exception.LBCommandArgsError(LBCommand.FILE_OR_LOGIC_MSG)
        super(ReplaceBlockCommand, self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd):
        cmd.replace_block.language = blox.connect.BloxCommand_pb2.LB
        cmd.replace_block.logic = self.logic
        if self.blockname is not None:
            cmd.replace_block.block_name = self.blockname



class RemoveBlockResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        self.block_names = lbcommand.blocknames
        if bloxcommand_response.remove_block.problems is not None:
            self.errors = bloxcommand_response.remove_block.problems

class RemoveBlockCommand(LBCommand):
    def __init__(self, blockname, workspace, **kw):
        super(RemoveBlockCommand, self).__init__(**kw)
        self.blocknames = blockname
        self.workspace = workspace

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, bloxcommand, req):
        bloxcommand.remove_block.block_name.extend(self.blocknames)



class AddLibraryResult(LBCommandResult): pass

class AddLibraryCommand(LBCommand):
    def __init__(self, name, workspace, **kw):
        super(AddLibraryCommand, self).__init__(**kw)
        self.name = name
        self.workspace = workspace

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.install_library.name = self.name



class AddProjectResult(LBCommandResult): pass

class AddProjectCommand(LBCommand):
    def __init__(self, workspace, norecurse, nocopy, libpath, **kw):
        self.workspace = workspace
        self.norecurse = norecurse
        self.nocopy = nocopy
        self.libpath = libpath
        self.dir = kw.pop('dir', '.')
        super(AddProjectCommand,self).__init__(**kw)
        if self.cwd is None:
          self.cwd = self.dir

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.install_project.projDir = os.path.abspath(self.dir)
        cmd.install_project.recurse = not self.norecurse
        cmd.install_project.copy = not self.nocopy
        cmd.install_project.lib_path = self.libpath



class InsertLogMessageResult(LBCommandResult): pass

class InsertLogMessageCommand(LBCommand):
    def __init__(self, workspace, message, **kw):
        super(InsertLogMessageCommand,self).__init__(**kw)
        self.workspace = workspace
        self.message = message

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.log_message.message = self.message




class ShutdownResult(LBAdminCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ShutdownResult, self).__init__(response, lbcommand, bloxcommand_response)
        self.message = response.shutdown_server.message

class ShutdownCommand(LBAdminCommand):
    def _decorate_request(self, req):
        req.client_id = '0'
        req.shutdown_server.waitForProcesses = False


class ServerLoglevelResult(LBAdminCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ServerLoglevelResult, self).__init__(response, lbcommand, bloxcommand_response)
        self.message = response.message or 'OK'

class ServerLoglevelCommand(LBAdminCommand):
    def __init__(self, loglevel, **kw):
        super(ServerLoglevelCommand, self).__init__(**kw)
        self.loglevel = loglevel

    def _decorate_request(self, req):
        req.client_id = '0'
        req.loglevel = self.loglevel


class AbortTransactionResult(LBAdminCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(AbortTransactionResult, self).__init__(response, lbcommand, bloxcommand_response)
        self.res = response

class AbortTransactionCommand(LBAdminCommand):
    def __init__(self, workspace, tid, **kw):
        super(AbortTransactionCommand, self).__init__(**kw)
        self.tid = tid
        self.workspace = workspace

    def _decorate_request(self, req):
        req.client_id = '0'
        if self.workspace is not None:
           req.abort_transaction.workspace = self.workspace
        req.abort_transaction.tid = self.tid


class CheckStatusResult(LBAdminCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(CheckStatusResult, self).__init__(response, lbcommand, bloxcommand_response)
        # print text_format.MessageToString(cmd.req)
        self.res = response
        self.server_status = True

class CheckStatusCommand(LBAdminCommand):
    def __init__(self, all, active, debug, workspace, **kw):
        super(CheckStatusCommand, self).__init__(**kw)
        self.active = active or all
        self.all = all
        self.debug = debug
        # in lb interactive, workspace will be a single workspace string
        if isinstance(workspace, str):
           if workspace != "":
              self.workspaces = [ workspace ]
           else:
              self.workspaces = [ ]
        else:
           self.workspaces = workspace

    def _decorate_request(self, req):
        for ws in self.workspaces:
           req.status.workspaces.append(ws)
        req.status.show_active_requests = self.active
        req.status.show_queued_requests = self.all
        req.status.add_debug_info = self.debug
        req.client_id = '0'
        self.req = req



class CloneWorkspaceResult(LBCommandResult): pass

class CloneWorkspaceCommand(LBCommand):
    def __init__(self, source, target, overwrite, **kw):
        super(CloneWorkspaceCommand,self).__init__(**kw)
        self.source = source
        self.target = target
        self.overwrite = overwrite
        self.kw = kw

    def run(self):
        tmpdir = tempfile.mktemp()
        try:
            ExportWorkspaceCommand(self.source, tmpdir, **self.kw).run()
            ImportWorkspaceCommand(self.target, tmpdir, self.overwrite, False, **self.kw).run()
        finally:
            shutil.rmtree(tmpdir)
        return self.target


class ImportProtobufResult(LBCommandResult): pass

class ImportProtobufCommand(LBCommand):
    def __init__(self, workspace, protocol, msgType, **kw):
        file_ = kw.pop('file', None)
        self.workspace = workspace
        self.protocol = protocol
        self.msgType = msgType
        if file_ is not None:
            self.messageStr = file_.read()

        super(ImportProtobufCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.import_protobuf.protocol = self.protocol
        cmd.import_protobuf.type_name = self.msgType
        cmd.import_protobuf.message = self.messageStr



class ExportProtobufResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        if hasattr(lbcommand,"fileName"):
            file = open(lbcommand.fileName, "w")
            file.write(bloxcommand_response.export_protobuf.message);
            file.close()
        else:
            has_msgCls = hasattr(lbcommand, "msgCls") and lbcommand.msgCls is not None
            if has_msgCls and issubclass(lbcommand.msgCls, Message):
                msgInstance = lbcommand.msgCls()
                msgInstance.ParseFromString(bloxcommand_response.export_protobuf.message)
                self.message = msgInstance

class ExportProtobufCommand(LBCommand):
    def __init__(self, workspace, protocol, msgType, file=None, msgCls=None, **kw):
        self.workspace = workspace
        self.protocol = protocol
        self.msgType = msgType
        self.readonly = True
        if file is not None:
            self.fileName = file.name
        self.msgCls = msgCls
        super(ExportProtobufCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.export_protobuf.protocol = self.protocol
        cmd.export_protobuf.type_name = self.msgType



class ProtoAddSpecResult(LBCommandResult): pass

class ProtoAddSpecCommand(LBCommand):
    def __init__(self, workspace, name, **kw):
        file_ = kw.pop('file', None)
        self.workspace = workspace
        self.name = name
        if file_ is not None:
            self.descriptor = file_.read()

        super(ProtoAddSpecCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.proto_add_spec.name = self.name
        cmd.proto_add_spec.descriptor_msg = self.descriptor



class GetProtocolDescriptorsResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        for proto in bloxcommand_response.proto_get_descriptors.protocols:
            file = open(proto.name + ".descriptor", "w")
            file.write(proto.descriptor_data)
            file.close
            print "Descriptor for %s written to file %s.descriptor" % (proto.name, proto.name)

class GetProtocolDescriptorsCommand(LBCommand):
    def  __init__(self, workspace, protocol, include=None, exclude=None, **kw):
        self.workspace = workspace
        self.protocol = protocol
        self.include = include
        self.exclude = exclude

        super(GetProtocolDescriptorsCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        if isinstance(self.protocol,list):
            cmd.proto_get_descriptors.all = False
            cmd.proto_get_descriptors.protocol_name.extend(self.protocol)
        else:
            cmd.proto_get_descriptors.all = True
            if self.include != None:
                cmd.proto_get_descriptors.include_regexp = self.include
            if self.exclude != None:
                cmd.proto_get_descriptors.exclude_regexp = self.exclude



class ImportXMLResult(LBCommandResult): pass

class ImportXMLCommand(LBCommand):
    def __init__(self, workspace, schema=None, **kw):
        self.workspace = workspace
        self.schema = schema
        file_ = kw.pop('file', None)
        if file_ is not None:
            self.document = file_.read()

        super(ImportXMLCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.import_xml_doc.document = self.document
        if self.schema is not None:
            cmd.import_xml_doc.schema = self.schema



class RawCommand():
    def __init__(self, conn, args, interactive, **kw):
        arg_dict = vars(args)
        if 'func' in arg_dict:
            del arg_dict['func']
        self.request = arg_dict["request"]
        self.isAdmin = arg_dict["isAdmin"]
        self.unixDomainSocket = arg_dict["unixDomainSocket"]
        self.verbose = arg_dict["verbose"]
        self.conn = conn

    @property
    def request_class(self):
        return blox.connect.ConnectBlox_pb2.Request

    @property
    def admin_request_class(self):
        return blox.connect.ConnectBlox_pb2.AdminRequest

    def run(self):
        req = None
        if self.isAdmin:
           req = self.admin_request_class()
        else:
           req = self.request_class()

        # set default request id defaulting to 0
        req.client_id = '0'
        text_format.Merge(self.request, req)

        if self.verbose:
           print "=" * 80
           print "Request:"
           print "-" * 80
           print text_format.MessageToString(req)
           print "-" * 80

        result = self.conn.call(req)

        if self.verbose:
           print "=" * 80
           print "Response:"
           print "-" * 80
        print text_format.MessageToString(result)

        if self.verbose:
           print "-" * 80



class XMLAddSpecResult(LBCommandResult): pass

class XMLAddSpecCommand(LBCommand):
    def __init__(self, workspace, name, **kw):
        file_ = kw.pop('file', None)
        self.workspace = workspace
        self.name = name
        if file_ is not None:
            self.descriptor = file_.read()

        super(XMLAddSpecCommand,self).__init__(**kw)

    def _decorate_request(self, req):
        self.initialize_transaction(req, self.workspace)
        self.bloxcommand = req.transaction.command.add()
        self._decorate_transaction_request(self.bloxcommand, req)

    def _decorate_transaction_request(self, cmd, req):
        cmd.xml_add_spec.name = self.name
        cmd.xml_add_spec.descriptor_msg = self.descriptor



class GetWorkspaceInfoResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(GetWorkspaceInfoResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.info = response.get_workspace_info

class GetWorkspaceInfoCommand(LBCommand):
    def __init__(self, name, **kw):
        super(GetWorkspaceInfoCommand, self).__init__(**kw)
        self.name = name

    def run(self):
        return super(GetWorkspaceInfoCommand, self).run()

    def _decorate_request(self, req):
        super(GetWorkspaceInfoCommand,self)._decorate_request(req)
        req.get_workspace_info.name = self.name



class StartMirrorResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(StartMirrorResult,self).__init__(response, lbcommand, bloxcommand_response)

class StartMirrorCommand(LBCommand):
    def __init__(self, name, host, remote_port, remote_workspace, **kw):
        super(StartMirrorCommand, self).__init__(**kw)
        self.name = name
        self.remote_host = host
        self.remote_port = remote_port
        self.remote_workspace = remote_workspace

    def run(self):
        return super(StartMirrorCommand, self).run()

    def _decorate_request(self, req):
        super(StartMirrorCommand,self)._decorate_request(req)
        req.start_mirror.name = self.name
        req.start_mirror.remote_host = self.remote_host
        req.start_mirror.remote_port = self.remote_port
        req.start_mirror.remote_workspace = self.remote_workspace



class StopMirrorResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(StopMirrorResult,self).__init__(response, lbcommand, bloxcommand_response)

class StopMirrorCommand(LBCommand):
    def __init__(self, name, **kw):
        super(StopMirrorCommand, self).__init__(**kw)
        self.name = name

    def run(self):
        return super(StopMirrorCommand, self).run()

    def _decorate_request(self, req):
        super(StopMirrorCommand,self)._decorate_request(req)
        req.stop_mirror.name = self.name



class PromoteMirrorResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(PromoteMirrorResult,self).__init__(response, lbcommand, bloxcommand_response)

class PromoteMirrorCommand(LBCommand):
    def __init__(self, name, **kw):
        super(PromoteMirrorCommand, self).__init__(**kw)
        self.name = name

    def run(self):
        return super(PromoteMirrorCommand, self).run()

    def _decorate_request(self, req):
        super(PromoteMirrorCommand,self)._decorate_request(req)
        req.promote_mirror.name = self.name



class CopyRemoteWorkSpaceResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(CopyRemoteWorkSpaceResult,self).__init__(response, lbcommand, bloxcommand_response)

class CopyRemoteWorkSpaceCommand(LBCommand):
    def __init__(self, name, host, remote_port, remote_workspace, **kw):
        super(CopyRemoteWorkSpaceCommand, self).__init__(**kw)
        self.name = name
        self.remote_host = host
        self.remote_port = remote_port
        self.remote_workspace = remote_workspace

    def run(self):
        return super(CopyRemoteWorkSpaceCommand, self).run()

    def _decorate_request(self, req):
        super(CopyRemoteWorkSpaceCommand,self)._decorate_request(req)
        req.copy_remote_workspace.name = self.name
        req.copy_remote_workspace.remote_host = self.remote_host
        req.copy_remote_workspace.remote_port = self.remote_port
        req.copy_remote_workspace.remote_workspace = self.remote_workspace


class ExtractExampleResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ExtractExampleResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.returned_data = response.execute_batch_script.returned_data

class ExtractExampleCommand(LBCommand):
    def __init__(self, name, predicate, transitive, monitor, defun, **kw):
        super(ExtractExampleCommand, self).__init__(**kw)
        self.workspace = name
        script = "extractExample"
        if predicate:
            script += " --predicate "
            script += predicate
        if transitive:
            script += " --transitive"
        if monitor:
            script += " --monitor"
        if defun is not None:
            for p in defun:
                script += " --defun "
                script += p
        self.script = script

    def run(self):
        return super(ExtractExampleCommand, self).run()

    def _decorate_request(self, req):
        super(ExtractExampleCommand,self)._decorate_request(req)
        req.execute_batch_script.workspace = self.workspace
        req.execute_batch_script.transactional = True
        req.execute_batch_script.return_data = True
        req.execute_batch_script.script = self.script
        self._decorate_with_authenticator(self.workspace, req)

class ExecuteBatchScriptResult(LBCommandResult):
    def __init__(self, response, lbcommand, bloxcommand_response):
        super(ExecuteBatchScriptResult,self).__init__(response, lbcommand, bloxcommand_response)
        self.output = response.execute_batch_script.output
        self.returned_data = response.execute_batch_script.returned_data

class ExecuteBatchScriptCommand(LBCommand):
    def __init__(self, script, workspace, file, transactional, return_data=None, **kw):
        super(ExecuteBatchScriptCommand, self).__init__(**kw)
        if script is None and file is None:
            raise lb_exception.LBCommandArgsError(
               "Either a filename or script text must be supplied.")
        self.workspace = workspace
        self.transactional = transactional
        self.return_data = return_data
        if file is not None:
            script = file.read()
        self.script = script

    def run(self):
        return super(ExecuteBatchScriptCommand, self).run()

    def _decorate_request(self, req):
        super(ExecuteBatchScriptCommand,self)._decorate_request(req)
        req.execute_batch_script.workspace = self.workspace
        req.execute_batch_script.script = self.script
        req.execute_batch_script.transactional = self.transactional
        if self.return_data is not None:
          req.execute_batch_script.return_data = self.return_data
        self._decorate_with_authenticator(self.workspace, req)
