# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: measure/measure_common.proto

import sys
_b=sys.version_info[0]<3 and (lambda x:x) or (lambda x:x.encode('latin1'))
from google.protobuf import descriptor as _descriptor
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
from google.protobuf import descriptor_pb2
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()


import blox.options_pb2


DESCRIPTOR = _descriptor.FileDescriptor(
  name='measure/measure_common.proto',
  package='lb.web.measure.common',
  serialized_pb=_b('\n\x1cmeasure/measure_common.proto\x12\x15lb.web.measure.common\x1a\x12\x62lox/options.proto\"\'\n\x08Location\x12\x0b\n\x03row\x18\x01 \x02(\x03\x12\x0e\n\x06\x63olumn\x18\x02 \x02(\x03\"f\n\x06Region\x12.\n\x05start\x18\x01 \x02(\x0b\x32\x1f.lb.web.measure.common.Location\x12,\n\x03\x65nd\x18\x02 \x02(\x0b\x32\x1f.lb.web.measure.common.LocationB\x1f\n\x1d\x63om.logicblox.bloxweb.measure')
  ,
  dependencies=[blox.options_pb2.DESCRIPTOR,])
_sym_db.RegisterFileDescriptor(DESCRIPTOR)




_LOCATION = _descriptor.Descriptor(
  name='Location',
  full_name='lb.web.measure.common.Location',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='row', full_name='lb.web.measure.common.Location.row', index=0,
      number=1, type=3, cpp_type=2, label=2,
      has_default_value=False, default_value=0,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='column', full_name='lb.web.measure.common.Location.column', index=1,
      number=2, type=3, cpp_type=2, label=2,
      has_default_value=False, default_value=0,
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
  serialized_start=75,
  serialized_end=114,
)


_REGION = _descriptor.Descriptor(
  name='Region',
  full_name='lb.web.measure.common.Region',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='start', full_name='lb.web.measure.common.Region.start', index=0,
      number=1, type=11, cpp_type=10, label=2,
      has_default_value=False, default_value=None,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='end', full_name='lb.web.measure.common.Region.end', index=1,
      number=2, type=11, cpp_type=10, label=2,
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
  serialized_start=116,
  serialized_end=218,
)

_REGION.fields_by_name['start'].message_type = _LOCATION
_REGION.fields_by_name['end'].message_type = _LOCATION
DESCRIPTOR.message_types_by_name['Location'] = _LOCATION
DESCRIPTOR.message_types_by_name['Region'] = _REGION

Location = _reflection.GeneratedProtocolMessageType('Location', (_message.Message,), dict(
  DESCRIPTOR = _LOCATION,
  __module__ = 'measure.measure_common_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.measure.common.Location)
  ))
_sym_db.RegisterMessage(Location)

Region = _reflection.GeneratedProtocolMessageType('Region', (_message.Message,), dict(
  DESCRIPTOR = _REGION,
  __module__ = 'measure.measure_common_pb2'
  # @@protoc_insertion_point(class_scope:lb.web.measure.common.Region)
  ))
_sym_db.RegisterMessage(Region)


DESCRIPTOR.has_options = True
DESCRIPTOR._options = _descriptor._ParseOptions(descriptor_pb2.FileOptions(), _b('\n\035com.logicblox.bloxweb.measure'))
# @@protoc_insertion_point(module_scope)