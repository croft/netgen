# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: lb/web/error_report.proto

import sys
_b=sys.version_info[0]<3 and (lambda x:x) or (lambda x:x.encode('latin1'))
from google.protobuf import descriptor as _descriptor
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
from google.protobuf import descriptor_pb2
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()




DESCRIPTOR = _descriptor.FileDescriptor(
  name='lb/web/error_report.proto',
  package='lb.web.error',
  serialized_pb=_b('\n\x19lb/web/error_report.proto\x12\x0clb.web.error\"/\n\x08Response\x12\x0e\n\x05\x65rror\x18\x9a\x05 \x01(\t\x12\x13\n\nerror_code\x18\x9b\x05 \x01(\tB\x17\n\x15\x63om.logicblox.bloxweb')
)
_sym_db.RegisterFileDescriptor(DESCRIPTOR)




_RESPONSE = _descriptor.Descriptor(
  name='Response',
  full_name='lb.web.error.Response',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='error', full_name='lb.web.error.Response.error', index=0,
      number=666, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='error_code', full_name='lb.web.error.Response.error_code', index=1,
      number=667, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  options=None,
  is_extendable=False,
  extension_ranges=[],
  oneofs=[
  ],
  serialized_start=43,
  serialized_end=90,
)

DESCRIPTOR.message_types_by_name['Response'] = _RESPONSE

Response = _reflection.GeneratedProtocolMessageType('Response', (_message.Message,), dict(
  DESCRIPTOR = _RESPONSE,
  __module__ = 'lb.web.error_report_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.error.Response)
  ))
_sym_db.RegisterMessage(Response)


DESCRIPTOR.has_options = True
DESCRIPTOR._options = _descriptor._ParseOptions(descriptor_pb2.FileOptions(), _b('\n\025com.logicblox.bloxweb'))
# @@protoc_insertion_point(module_scope)
