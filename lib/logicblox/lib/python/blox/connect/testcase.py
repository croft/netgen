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

import unittest
import copy
import blox.connect.io
from google.protobuf import text_format

class TestCase(unittest.TestCase):

   def setUp(self):
       if hasattr(self, 'unixDomainSocket'):
           self.conn = blox.connect.io.Connection(False, self.unixDomainSocket)
       else:
           self.conn = blox.connect.io.Connection(False)
       self.conn.open()

   def tearDown(self):
       self.conn.close()

   def assertMessageContains(self, msg1, msg2):
       m2 = text_format.MessageToString(msg2)
       self.assertIn(msg1, m2)

   def assertMessageEqual(self, msg1, msg2):
       if isinstance(msg2, basestring):
          notext_msg2 = copy.copy(msg1)
          notext_msg2.Clear()
          text_format.Merge(msg2, notext_msg2)
          
          m1 = text_format.MessageToString(msg1)
          m2 = text_format.MessageToString(notext_msg2)
          self.assertEqual(m1, m2)
          
       else:
          m1 = text_format.MessageToString(msg1)
          m2 = text_format.MessageToString(msg2)
          self.assertEqual(m1, m2)

   def assertRelationEqual(self, rel1, rel2_maybeText):
       # if second parameter is string then make message from it
       if isinstance(rel2_maybeText, basestring):
          rel2 = copy.copy(rel1)
          rel2.Clear()
          text_format.Merge(rel2_maybeText, rel2)
       else:
          rel2 = rel2_maybeText

       self.assertEqual(rel1.HasField('name'), rel2.HasField('name'))
       if rel1.HasField('name'):
          self.assertEqual(rel1.name, rel2.name)
       self.assertEqual(len(rel1.column), len(rel2.column))
       for col1, col2 in zip(rel1.column, rel2.column):
          for col in [col1, col2]:
             # We here perform a normalization for entity columns
             if col.HasField('entity_column'):
                entity_column = col.entity_column
                if entity_column.HasField('index_values'):
                   # We remove the index values
                   entity_column.index_values.Clear()
                if entity_column.HasField('refmode_values'):
                   refmode_values = entity_column.refmode_values
                   for (FieldDescriptor, col_values) in refmode_values.ListFields():
                      col_values.values.sort()
          
          self.assertMessageEqual(col1, col2)

   def assertHasField(self, msg, fieldname):
       self.assertTrue(msg.HasField(fieldname))

   def assertNotHasField(self, msg, fieldname):
       self.assertFalse(msg.HasField(fieldname))

   def executeLogic(self, ws, logic):
       req = blox.connect.ConnectBlox_pb2.Request()
       req.transaction.workspace = ws
       cmd = req.transaction.command.add()
       cmdexec = getattr(cmd, 'exec')
       cmdexec.logic = logic
       return self.conn.call(req)       

   def addCmdAddBlock(self, msg, logic):
       cmd = msg.command.add()
       cmd.add_block.active = True
       cmd.add_block.logic = logic

   def addLogic(self, ws, logic):
       req = blox.connect.ConnectBlox_pb2.Request()
       req.transaction.workspace = ws
       cmd = req.transaction.command.add()
       cmd.add_block.active = True
       cmd.add_block.logic = logic
       return self.conn.call(req)       

   def create_workspace(self, connection):
       req = blox.connect.ConnectBlox_pb2.Request()
       req.create.measure_engine = False # just to initialize the create request
       response = connection.call(req)
       self.assertHasField(response, "create")
       self.assertHasField(response.create, "name")
       return response.create.name

   def delete_workspace(self, connection, wspath):
       req = blox.connect.ConnectBlox_pb2.Request()
       cmd = req.delete.name = wspath
       response = connection.call(req)
       self.assertMessageEqual(response, "delete {}")

   # returns protobuf relation
   def queryPredicate(self, ws, predname):
       req = blox.connect.ConnectBlox_pb2.Request()
       req.transaction.workspace = ws
       cmd = req.transaction.command.add()
       cmd.query_predicate.predicate.global_name.qualified_name = predname
       response = self.conn.call(req)
       return response.transaction.command[0].query_predicate.relation

   def printMessage(self, msg):
       print "---------------------------------------- "
       print text_format.MessageToString(msg)
       print "---------------------------------------- "
