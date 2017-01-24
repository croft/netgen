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
import sys
import os
import socket
import blox.connect.ConnectBloxAsync_pb2

DEFAULT_ADMIN_PORT = 55182

class AsyncConnection:
  """ConnectBlox Async Connection"""

  def __init__(self):
    self.port = os.getenv('LB_CONNECTBLOX_ASYNC_SERVER_ADMIN_PORT', DEFAULT_ADMIN_PORT)
    if not isinstance(self.port, int) and not self.port.isdigit():
       raise RuntimeError("Connection port must be an integer but is %s" % self.port) 

    self.port = int(self.port) 
    self.host = "localhost"
    self.reqid = 0
    self.response_buffer = {}

  # returns response message
  def call(self, req):

    request_id = self.send(req)
    response_id, response =  self.receive_next()

    if response_id != request_id:
       raise RuntimeError("request/response id mismatch")

    return response

  # returns a request_id
  def send(self, msg):
    txt = msg.SerializeToString()
    self.reqid = self.reqid + 1;
    self.sendsize(self.reqid)
    self.sendsize(len(txt))
    self.sock.sendall(txt)
    return self.reqid

  # returns a tuple of response_id and message
  def receive_next(self):
    response = blox.connect.ConnectBloxAsync_pb2.AsyncAdminResponse()
    response_id = self.readsize()
    msglen = self.readsize()
    serialized = self.receiveall(msglen)
    response.ParseFromString(serialized)
    return (response_id, response)

  def receiveall(self, msglen):
    msg = []
    while msglen:
      chunk = self.sock.recv(msglen)
      if len(chunk) == 0:
        raise RuntimeError("socket connection broken")
      msg.append(chunk)
      msglen -= len(chunk)
    return "".join(msg)


  def sendsize(self, x):
    b1 = ((x >> 24) & 0xff)
    b2 = ((x >> 16) & 0xff)
    b3 = ((x >> 8)  & 0xff)
    b4 = ((x >> 0)  & 0xff)
    b = bytearray([b1, b2, b3, b4])
    self.sock.sendall(b)

  def readsize(self):
    s = self.receiveall(4)
    b = bytearray(s)   
    return ((b[0] & 0xff) << 24) | ((b[1] & 0xff) << 16) | ((b[2] & 0xff) << 8) | ((b[3] & 0xff) << 0);

  def open(self):
    self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    self.sock.connect((self.host, self.port))
    self.sock.setsockopt(socket.SOL_TCP, socket.TCP_NODELAY, 1)


