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


"""
Helper classes for implementing TPC drivers when using LogicBlox.
Usage of this module involves the classes LBExecutor and LBInactiveBlock.

This module currently only supports a subset of the types used in LB,
specifically the subset used in TPC implementations.

LBExecutor helps in abstracting a connectblox session against a given
workspace, which simplifies the API for repeated calls to the same
workspace.

LBInactiveBlock represents an inactive block within said workspace,
and simplifies the interface to specify input bindings and getting
results back.
"""

import os
import sys
import decimal
import operator
import optparse
import csv
import datetime

from dbcommands import lb_command
import blox.connect.io
from blox.connect.BloxCommand_pb2 import InputBinding

#
# Callable object representing an inactive block
#
class LBInactiveBlock(object):
   ''' 
   Represents a callable inactive block, with a call method to invoke.
  
   An inactive block in LB will use local predicates for inputs and outputs,
   without any explicit marking of which predicates are which. This class lets
   you specify the predicates to use as inputs and the ones to use as outputs.
   For each input predicate, it is necessary to specify the signature of the
   predicate, to know what to expect when calling the block. For the output
   predicates, only the names of the predicates are necessary, since we can
   introspect the response to determine how to return results.

   Each input predicate is specified as a keyword argument to the constructor,
   and its value is given as a sequence of types (enumeration is in LBType).
   If a single type is given (i.e. not an enumeration), we assume that the
   predicate is a unary predicate.

   For instance, a block such as:

      _input1[x] = n -> string(x), int(n).
      _input2(y) -> decimal(y).

   can be represented by:

      block = LBInactiveBlock(..., _input1=(STRING, INT), _input2=DECIMAL, ...)

   When calling the block, you use the same keyword arguments to specify the
   actual tuples being passed in, with the values being a sequence of tuples
   containing objects of the correct types. A single tuple can be passed
   without the containing sequence, and a single value can be passed if the
   input is a unary predicate. Additionally, a sequence of values will be
   treated as a sequence of tuples if the predicate is a unary predicate.

   For instance, calls of the above block could be:

      resp = block.call( _input1=[("a", 1), ("b", 2)], _input2=3.2 )
      resp = block.call( _input1=("c",3), _input2=[4.3, 5.4] )

   Responses are returned as a dictionary, keyed by the output predicate, whose
   values are a sequence of tuples.

   Note:
   This is bound to a particular LBExecutor. We may want to reconsider this
   approach, if we are using multiple different executors for multiple streams,
   and we want to reuse block objects, although a better approach might be to
   allow re-binding an object to a new executor.
   '''

   def __init__(self, executor, name, readonly=False, outputs=[], **param_types):
      ''' 
      Create a callable inactive block.
      @param executor the executor this block is bound to.
      @param name the name of the inactive block in the workspace.
      @param readonly boolean indicating whether a call is readonly or not.
      @param outputs sequence of output predicate names
      @param param_types remaining keyword args interpreted as input preds (see class docs)
      '''
      self.executor = executor
      self.name = name
      self.readonly = readonly
      self.outputs = outputs
      if not hasattr(self.outputs, '__iter__'):
         self.outputs = [self.outputs]

      self.param_types = param_types     # Dict of predname to seq of type enums
      self.param_bindings = {}           # Dict of predname to InputBinding object
      self.param_vals = {}               # Dict of predname to seq of protobuf values objects

      for p in self.param_types.keys():
         self._prepare_bindings(p)

   def _prepare_bindings(self, pred_name):
      '''
      Cache input bindings for later usages of object
      '''
      ib = InputBinding()
      ib.name = pred_name

      types = self.param_types[pred_name]
      if hasattr(types, '__iter__'):
         vals = []
         for t in types:
            vals.append(self._get_value_col(ib, t))
      else:
         vals = self._get_value_col(ib, types)

      self.param_bindings[pred_name] = ib
      self.param_vals[pred_name] = vals

   def _get_value_col(self, ib, t):
      '''
      Get reference to correct column in inputbinding for given type
      '''
      if t == LBType.INT64:
         return ib.relation.column.add().int64_column.values
      elif t == LBType.STRING:
         return ib.relation.column.add().string_column.values
      elif t == LBType.DECIMAL:
         return ib.relation.column.add().decimal_column.values
      elif t == LBType.DATETIME:
         return ib.relation.column.add().datetime_column.values
      else:
         raise Exception("Unknown type {0}".format(t))
 

   def call(self, **all_params):
      '''
      Invoke the inactive block.
      @param all_params the inputs where keyword is predicate, and value is sequence of tuples
      @return results as dictionary keyed by output predicate name, values being sequence of tuples.
      '''

      for input_pred in all_params.keys():
         if not input_pred in self.param_types.keys():
            raise Exception("Found input params for unknown predicate {0}".format(input_pred))

         types = self.param_types[input_pred]
         vals = self.param_vals[input_pred]
         ib = self.param_bindings[input_pred]
         params = all_params[input_pred]

         # Clear existing values from protobuf
         if hasattr(vals, '__iter__'):
            for v in vals:
               del v[:]
         else:
            del vals[:]
       
         if hasattr(types, '__iter__'):
            if hasattr(params, '__iter__'):
               p0 = params[0]
               if hasattr(p0, '__iter__'):
                  self._serialize_seq_seq(types, vals, params)
               else:
                  self._serialize_single_tuple(types, vals, params)
            else:
               raise Exception("Single value passed for non-scalar predicate {0}".format(input_pred))
         else: 
            if hasattr(params, '__iter__'):
               self._serialize_seq_values(types, vals, params)
            else:
               self._serialize_single_value(types, vals, params)

      resp = self.executor.exec_block(self.name, self.param_bindings.values(), self.outputs, self.readonly)
      return resp

   def _serialize_seq_seq(self, types, vals, params):
      for tup in params:
         self._serialize_single_tuple(types, vals, tup)

   def _serialize_single_tuple(self, types, vals, params):
      if len(vals) != len(params):
         raise Exception("Input params differ in length from specs")
      for (t,v,p) in zip(types, vals, params):
         self._serialize_single_value(t, v, p)

   def _serialize_seq_values(self, types, vals, params):
      for p in params:
         self._serialize_single_value(types, vals, p)

   def _serialize_single_value(self, t, v, p):
      param = p
      if t == LBType.DECIMAL:
         param = int(p * 100000)
      v.append(param)


#
# Class representing a persistent connection, and bound to a specific workspace.
#
class LBExecutor(object):
   ''' 
   Wrapper around lb_command functions and blox.connect.io functions, to
   represent a connectblox session bound to a given workspace, to ease
   the usage of the API.
   Each call of one of the public functions is a complete command invocation.
   '''
   
   def __init__(self, workspace, cwd=None):
      '''
      Create an executor for a given workspace. Opens a connection and keeps
      it open until close() is called.
      @param workspace the name of the workspace to issue calls against.
      @param cwd directory to use as current dir for file predicates.
      '''
      self.workspace = workspace
      self.conn = blox.connect.io.Connection(False)
      self.conn.open()
      self.cwd = cwd
  
   def close(self):
      ''' Close the connection '''
      self.conn.close()

   def create_workspace(self):
      ''' 
      Create the workspace we are bound to.
      '''
      cmd = lb_command.CreateWorkspaceCommand(self.workspace, False, True)
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
      Note - possibly should return LBInactiveBlock?
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

   def exec_block(self, block_name, input_bindings, output_preds, readonly):
      '''
      Execute a stored block, with optional output_preds to indicate what
      list of tuples to return. output_preds should be a list of prednames
      Returns a dictionary of {predname:list_of_tuples}
      Used by LBInactiveBlock, but can also be called directly, for instance
      when calling import blocks that don't have inputs/outputs. Otherwise,
      LBInactiveBlock is much easier to use.

      @param block_name name of the block to execute
      @param input_bindings sequence of protobuf InputBinding objects, or None.
      @param output_preds sequence of output pred names or None.
      @param readonly boolean indicator if block should be invoked readonly.
      '''

      cmd = lb_command.ExecuteBlockCommand(
         name = block_name,
         workspace = self.workspace,
         escape = False,
         conn = self.conn,
         readonly = readonly,
         should_print = output_preds,
         inputs = input_bindings)

      result = cmd.run()

      tuple_dict = {}
      if len(output_preds) > 0:
         for o in output_preds:
            tuple_dict[o] = self._extract_tuples(result, o)

      return tuple_dict


   def _extract_tuples(self, result, pred_name):
      """ 
      Crazy stuff to extract tuples from connectblox response.
      Note - candidate for optimization, can keep column extractors in LBInactiveBlock.
      """
      if (not hasattr(result, 'output_relations')):
         raise Exception("no output predicates in result")

      relation = None
      for rt in result.output_relations:
         if rt[0] == pred_name:
            relation = rt[1]

      if relation == None:
         raise Exception("did not find {0} predicate in result".format(pred_name))

      # Create column extractors for each column
      self.extractors=[]
      for col in relation.column:
         self.extractors.append(ColumnExtractor.create(col))

      tuples=[]
      for i in range(self.extractors[0].len):
         value_tuple = tuple(map(lambda c: c.get_value(i), self.extractors))
         tuples.append(value_tuple)

      return tuples

 
   def exec_logic(self, logic, output_preds=[], readonly=False, block_name=None):
      '''
      Execute arbitrary logic against workspace, in temporary block.
      @param logic string containing logic to execute
      @param output_preds list of output predicate names to return
      @param readonly boolean indicator of whether to exec readonly
      @return dictionary keyed by output predicate, values being sequence of tuples
      ''' 
      cmd = lb_command.ExecuteLogicCommand( 
         workspace=self.workspace, 
         conn=self.conn,
         cwd = self.cwd,
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

   def exec_logic_from_file(self, filename, output_preds=[], readonly=False, block_name=None):
      ''' Helper to exec logic from a file instead of a string. '''
      with open(filename, 'r') as f:
         logic = f.read()
      self.exec_logic(logic, output_preds, readonly, block_name) 

   def add_block_from_file(self, filename):
      ''' Helper to add block from a file instead of a string. '''
      with open(filename, "r") as f:
         logic = f.read()
      self.add_block(os.path.basename(filename), logic)





class UTC(datetime.tzinfo):
   '''
   Helper class to deal with datetime handling. Required by python APIs.
   '''
   def utcoffset(self, dt):
      return datetime.timedelta(0)
   def tzname(self, dt):
      return "UTC"
   def dst(self, dt):
      return datetime.timedelta(0)

#
# Class to extract values from a protobuf Column object. Provides key
# api to print out nth value from the column. Always returned as string,
# formatted according to tpc-h specs
# Provides a factory method to create a ColumnPrinter from a Column object.
#
class ColumnExtractor():
   '''
   Class to extract values from connectblox protobuf Column objects.
   Not meant for direct usage by clients of this module.
   Used when executing blocks that return a response, to transform
   returned values as python objects in an easy way, mostly by providing
   conversion functions where this is not a direct mapping, and a factory
   method to test which type a given column has, by testing the optional
   members.
   '''

   def __init__(self, column, get_func, len):
      '''
      @param column the connectblox column object to extract values from.
      @param get_func the function used to extract and convert individual column values.
      @param len number of values in the column.
      '''
      self.get_func = get_func
      self.column = column
      self.len = len

   def _get_string_value(self, n):
      return self.column.string_column.values[n]

   def _get_int64_value(self, n):
      return self.column.int64_column.values[n]

   def _get_decimal_value(self, n):
      i = self.column.decimal_column.values[n]
      i_abs = abs(i)
      before_point = i_abs / 100000
      before_point_dec = decimal.Decimal(before_point)
      after_point = i_abs % 100000
      after_point_dec = decimal.Decimal(after_point) / 100000
      val = before_point_dec + after_point_dec
      if (i != i_abs):
    val = -val
      val = val.quantize(decimal.Decimal('0.01'), decimal.ROUND_HALF_UP)
      return val

   def _get_datetime_value(self, n):
      dt = datetime.datetime.fromtimestamp(self.column.datetime_column.values[n], UTC())
      return datetime.date(dt.year,dt.month,dt.day)

   def get_value(self, n):
      ''' 
      Get the nth value from the bound column. Note that this is not bounds checked!
      @param n index of value in column to fetch.
      '''
      return self.get_func(self, n)

   @staticmethod
   def create(column):
      '''
      Create an extractor for a given protobuf column.
      @param column connectblox protobuf column object to bind response to.
      '''
      if (column.HasField("string_column")):
         return ColumnExtractor(column, ColumnExtractor._get_string_value, 
                                len(column.string_column.values))
      if (column.HasField("int64_column")):
         return ColumnExtractor(column, ColumnExtractor._get_int64_value, 
                                len(column.int64_column.values))
      if (column.HasField("decimal_column")):
         return ColumnExtractor(column, ColumnExtractor._get_decimal_value, 
                                len(column.decimal_column.values))
      if (column.HasField("datetime_column")):
         return ColumnExtractor(column, ColumnExtractor._get_datetime_value,
                                len(column.datetime_column.values))   
      raise Exception("Unknown column type")
      

class LBType:
   '''
   Enumeration of supported types in connectblox, for API friendliness.
   '''
   INT64    = 1
   STRING   = 2
   DECIMAL  = 3
   DATETIME = 4