# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: lb/web/protobuf_meta.proto

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
  name='lb/web/protobuf_meta.proto',
  package='lb.web.protometa',
  serialized_pb=_b('\n\x1alb/web/protobuf_meta.proto\x12\x10lb.web.protometa\"R\n\x13ProtoBufMetaRequest\x12;\n\x08protocol\x18\x01 \x01(\x0b\x32).lb.web.protometa.ProtoBufProtocolRequest\"\x19\n\x17ProtoBufProtocolRequest\"T\n\x14ProtoBufMetaResponse\x12<\n\x08protocol\x18\x01 \x01(\x0b\x32*.lb.web.protometa.ProtoBufProtocolResponse\"\x90\x01\n\x18ProtoBufProtocolResponse\x12\x1c\n\x14request_message_name\x18\x01 \x01(\t\x12\x1a\n\x12request_descriptor\x18\x02 \x01(\x0c\x12\x1d\n\x15response_message_name\x18\x03 \x01(\t\x12\x1b\n\x13response_descriptor\x18\x04 \x01(\x0c\x42 \n\x1e\x63om.logicblox.bloxweb.protobuf')
)
_sym_db.RegisterFileDescriptor(DESCRIPTOR)




_PROTOBUFMETAREQUEST = _descriptor.Descriptor(
  name='ProtoBufMetaRequest',
  full_name='lb.web.protometa.ProtoBufMetaRequest',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='protocol', full_name='lb.web.protometa.ProtoBufMetaRequest.protocol', index=0,
      number=1, type=11, cpp_type=10, label=1,
      has_default_value=False, default_value=None,
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
  serialized_start=48,
  serialized_end=130,
)


_PROTOBUFPROTOCOLREQUEST = _descriptor.Descriptor(
  name='ProtoBufProtocolRequest',
  full_name='lb.web.protometa.ProtoBufProtocolRequest',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
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
  serialized_start=132,
  serialized_end=157,
)


_PROTOBUFMETARESPONSE = _descriptor.Descriptor(
  name='ProtoBufMetaResponse',
  full_name='lb.web.protometa.ProtoBufMetaResponse',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='protocol', full_name='lb.web.protometa.ProtoBufMetaResponse.protocol', index=0,
      number=1, type=11, cpp_type=10, label=1,
      has_default_value=False, default_value=None,
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
  serialized_start=159,
  serialized_end=243,
)


_PROTOBUFPROTOCOLRESPONSE = _descriptor.Descriptor(
  name='ProtoBufProtocolResponse',
  full_name='lb.web.protometa.ProtoBufProtocolResponse',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='request_message_name', full_name='lb.web.protometa.ProtoBufProtocolResponse.request_message_name', index=0,
      number=1, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='request_descriptor', full_name='lb.web.protometa.ProtoBufProtocolResponse.request_descriptor', index=1,
      number=2, type=12, cpp_type=9, label=1,
      has_default_value=False, default_value=_b(""),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='response_message_name', full_name='lb.web.protometa.ProtoBufProtocolResponse.response_message_name', index=2,
      number=3, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='response_descriptor', full_name='lb.web.protometa.ProtoBufProtocolResponse.response_descriptor', index=3,
      number=4, type=12, cpp_type=9, label=1,
      has_default_value=False, default_value=_b(""),
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
  serialized_start=246,
  serialized_end=390,
)

_PROTOBUFMETAREQUEST.fields_by_name['protocol'].message_type = _PROTOBUFPROTOCOLREQUEST
_PROTOBUFMETARESPONSE.fields_by_name['protocol'].message_type = _PROTOBUFPROTOCOLRESPONSE
DESCRIPTOR.message_types_by_name['ProtoBufMetaRequest'] = _PROTOBUFMETAREQUEST
DESCRIPTOR.message_types_by_name['ProtoBufProtocolRequest'] = _PROTOBUFPROTOCOLREQUEST
DESCRIPTOR.message_types_by_name['ProtoBufMetaResponse'] = _PROTOBUFMETARESPONSE
DESCRIPTOR.message_types_by_name['ProtoBufProtocolResponse'] = _PROTOBUFPROTOCOLRESPONSE

ProtoBufMetaRequest = _reflection.GeneratedProtocolMessageType('ProtoBufMetaRequest', (_message.Message,), dict(
  DESCRIPTOR = _PROTOBUFMETAREQUEST,
  __module__ = 'lb.web.protobuf_meta_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.protometa.ProtoBufMetaRequest)
  ))
_sym_db.RegisterMessage(ProtoBufMetaRequest)

ProtoBufProtocolRequest = _reflection.GeneratedProtocolMessageType('ProtoBufProtocolRequest', (_message.Message,), dict(
  DESCRIPTOR = _PROTOBUFPROTOCOLREQUEST,
  __module__ = 'lb.web.protobuf_meta_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.protometa.ProtoBufProtocolRequest)
  ))
_sym_db.RegisterMessage(ProtoBufProtocolRequest)

ProtoBufMetaResponse = _reflection.GeneratedProtocolMessageType('ProtoBufMetaResponse', (_message.Message,), dict(
  DESCRIPTOR = _PROTOBUFMETARESPONSE,
  __module__ = 'lb.web.protobuf_meta_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.protometa.ProtoBufMetaResponse)
  ))
_sym_db.RegisterMessage(ProtoBufMetaResponse)

ProtoBufProtocolResponse = _reflection.GeneratedProtocolMessageType('ProtoBufProtocolResponse', (_message.Message,), dict(
  DESCRIPTOR = _PROTOBUFPROTOCOLRESPONSE,
  __module__ = 'lb.web.protobuf_meta_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.protometa.ProtoBufProtocolResponse)
  ))
_sym_db.RegisterMessage(ProtoBufProtocolResponse)


DESCRIPTOR.has_options = True
DESCRIPTOR._options = _descriptor._ParseOptions(descriptor_pb2.FileOptions(), _b('\n\036com.logicblox.bloxweb.protobuf'))
# @@protoc_insertion_point(module_scope)
