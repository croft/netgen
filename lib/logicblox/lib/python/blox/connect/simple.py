"""
Copyright 2016 LogicBlox, Inc.

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

import os.path
import blox.connect.io
import blox.connect.BloxCommand_pb2 as proto
from dbcommands import lb_command
import relations

class Session(object):
   '''
   Wrapper around lb_command functions and blox.connect.io functions, to
   represent a connectblox session bound to a given workspace, to ease
   the usage of the API.
   Each call of one of the public functions is a complete command invocation.
   '''
   
   def __init__(self, workspace, connection=None, cwd=None, commit_mode=None):
       '''
       Create a session for a given workspace. Opens a connection and keeps
       it open until close() is called.
       @param workspace the name of the workspace to issue calls against.
       @param cwd directory to use as current dir for file predicates.
       @param commit_mode mode to determine when the response for the
          transaction is sent back to the client. Possible values:
          'softcommit', 'diskcommit' or None (use the server default).
       '''
       self.workspace = workspace
       self.conn = connection
       if self.conn is None:
           self.conn = blox.connect.io.Connection(False)
       self.conn.open()
       self.cwd = cwd
       self.commit_mode = commit_mode
  
   def close(self):
       ''' Close the connection '''
       self.conn.close()

   def create_workspace(self, overwrite = True):
       ''' 
       Create the workspace of the session
       '''
       cmd = lb_command.CreateWorkspaceCommand(
           conn = self.conn,
           name = self.workspace,
           unique = False,
           overwrite = overwrite)
       result = cmd.run()

   def create_branch(self, name, parent = None, overwrite = False):
       cmd = lb_command.CreateBranchCommand(
           conn = self.conn,
           workspace = self.workspace,
           name = name,
           parent = parent,
           overwrite = overwrite)
       result = cmd.run()

   def replace_default_branch(self, name):
       cmd = lb_command.DefaultBranchCommand(
           conn = self.conn,
           workspace = self.workspace,
           name = name)
       result = cmd.run()

   def add_block(self, block_name, logic):
      '''
      Add an active block, with the supplied logic.
      @param block_name the name of the block to create
      @param logic string containing logic to add.
      '''
      cmd = lb_command.AddBlockCommand(
         conn = self.conn,
         name = block_name,
         workspace = self.workspace,
         measure = False,
         logic = logic)
      result = cmd.run()

   def add_inactive_block(self, block_name, logic):
      '''
      Add an inactive block.

      @param block_name name of the block to add.
      @param logic string containing logic to add.
      '''
      cmd = lb_command.AddBlockCommand(
         conn = self.conn,
         name = block_name,
         workspace = self.workspace,
         measure = False,
         active = False,
         logic = logic)
      result = cmd.run()

   def exec_block(self, block_name, input_bindings = {}, output_preds = [], readonly = False,
                  cwd = None, commit_mode = None):
      '''
      Execute a stored block, with optional output_preds to indicate what
      list of tuples to return. output_preds should be a list of prednames
      Returns a dictionary of {predname:list_of_tuples}

      @param block_name name of the block to execute
      @param input_bindings sequence of protobuf InputBinding objects, or None.
      @param output_preds sequence of output pred names or None.
      @param readonly boolean indicator if block should be invoked readonly.
      @param cwd directory to use as current dir for file predicates. Overrides
         __init__'s cwd.
      @param commit_mode mode to determine when the response for the
         transaction is sent back to the client. Possible values:
         'softcommit', 'diskcommit' or None (use the server default).
         Overrides __init__'s commit_mode.
      '''
      inputs = []
      for key, value in input_bindings.iteritems():
          rel = relations.SimpleRelation()
          rel.extend(value)

          input = proto.InputBinding()
          input.name = key
          input.relation.MergeFrom(rel.get_proto())
          inputs.append(input)

      cmd = lb_command.ExecuteBlockCommand(
         conn = self.conn,
         name = block_name,
         workspace = self.workspace,
         cwd = cwd or self.cwd,
         commit_mode = commit_mode or self.commit_mode,
         escape = False,
         readonly = readonly,
         should_print = output_preds,
         inputs = inputs)

      result = cmd.run()

      tuple_dict = {}
      if len(output_preds) > 0:
         for o in output_preds:
            tuple_dict[o] = self._extract_tuples(result, o)

      return tuple_dict


   def _extract_tuples(self, result, pred_name):
      if (not hasattr(result, 'output_relations')):
         raise Exception("no output predicates in result")

      relation = None
      for rt in result.output_relations:
         if rt[0] == pred_name:
            relation = rt[1]

      if relation is None:
         raise Exception("did not find {0} predicate in result".format(pred_name))

      rel = relations.SimpleRelation()
      rel.set_proto(relation)
      return list(rel)
 
   def exec_logic(self, logic, output_preds=[], readonly=False, block_name=None,
                  cwd=None, commit_mode=None):
      '''
      Execute arbitrary logic against workspace, in temporary block.
      @param logic string containing logic to execute
      @param output_preds list of output predicate names to return
      @param readonly boolean indicator of whether to exec readonly
      @param cwd directory to use as current dir for file predicates. Overrides
         __init__'s cwd.
      @param commit_mode mode to determine when the response for the
         transaction is sent back to the client. Possible values:
         'softcommit', 'diskcommit' or None (use the server default).
         Overrides __init__'s commit_mode.
      @return dictionary keyed by output predicate, values being sequence of tuples
      ''' 
      cmd = lb_command.ExecuteLogicCommand( 
         workspace=self.workspace, 
         conn = self.conn,
         cwd = cwd or self.cwd,
         commit_mode = commit_mode or self.commit_mode,
         escape = False,
         logic = logic,
         readonly = readonly,
         block_name = block_name,
         should_print = output_preds)
      result = cmd.run()

      tuple_dict = {}
      if len(output_preds) > 0:
         for o in output_preds:
            tuple_dict[o] = self._extract_tuples(result, o)

      return tuple_dict

   def exec_logic_from_file(self, filename, output_preds=[], readonly=False, block_name=None,
                            cwd=None, commit_mode=None):
      ''' Helper to exec logic from a file instead of a string. '''
      with open(filename, 'r') as f:
         logic = f.read()
      self.exec_logic(logic, output_preds, readonly, block_name, cwd, commit_mode)

   def add_block_from_file(self, filename):
      ''' Helper to add block from a file instead of a string. '''
      with open(filename, "r") as f:
         logic = f.read()
      self.add_block(os.path.basename(filename), logic)
