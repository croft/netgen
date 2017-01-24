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

import decimal
import types
import datetime

import blox.connect.BloxCommand_pb2 as proto

def column_fields():
    return ["bool_column",
            "int64_column",
            "uint64_column",
            "float64_column",
            "string_column",
            "datetime_column",
            "decimal128_column",
            "int128_column"]

def col_count(rel):
    return len(rel.column)

def row_count(rel):
    for col in rel.column:
       return colrow_count(col)
    return 0

def colrow_count(col):
   if col.HasField('entity_column'):
      if col.entity_column.HasField('index_values'):
         return colrow_count(col.entity_column.index_values)
      else:
         return colrow_count(col.entity_column.refmode_values)
   elif col.HasField('decimal128_column'):
       return len(col.decimal128_column.integral_digits)
   elif col.HasField('int128_column'):
       return len(col.int128_column.high)
   else:
       for t in column_fields():
          if col.HasField(t):
             values = getattr(col, t).values
             return len(values)
       return 0

def print_index_cell(col, i):
    return "[%s]" % str(col.uint64_column.values[i])

def print_separator(i):
    return " "

escape_table = {
   '"'  : '\\"',
   '\n' : "\\n",
   '\t' : "\\t",
   '\r' : "\\r",
}

def formatter_string(s):
    s = "\"" + ''.join(escape_table.get(c, c) for c in s) + "\""
    return str(s.encode('utf_8'))

def formatter_boolean(b):
    if b:
       return "true"
    if not b:
       return "false"
    else:
       return "not-a-boolean"

def formatter_datetime(s):
    return datetime.datetime.utcfromtimestamp(s).isoformat(' ') + '+00:00'

def formatter_decimal(negative, integral, fraction):
    v = serialized_decimal128_to_decimal(negative, integral, fraction)
    return '{0:g}'.format(v)

def formatter_int128(high, low):
    v = 18446744073709551616*high + low
    if v >= 170141183460469231731687303715884105728:
        v = v - 340282366920938463463374607431768211456
    return str(v)

def serialized_decimal128_to_decimal(negative, integral, fraction):
    billion = 1000000000L;
    unscaled = integral * billion * billion + fraction;
    if negative:
        unscaled *= -1
    return decimal.Decimal(unscaled) / (billion * billion)

def formatter_string_noescape(s):
    return str(s.encode('utf_8'))

class RelationPrinter(object):
  """Utility class for printing relations"""

  def __init__(self, rel):
    self.rel = rel

    self.formatter = {}
    self.formatter["bool_column"] = formatter_boolean
    self.formatter["int64_column"] = str
    self.formatter["uint64_column"] = str
    self.formatter["float64_column"] = repr
    self.formatter["string_column"] = formatter_string
    self.formatter["datetime_column"] = formatter_datetime
    self.formatter["decimal128_column"] = formatter_decimal
    self.formatter["int128_column"] = formatter_int128
    self.formatter["color_column"] = str

    self.print_entity_indexes = True
    self.delimiter = ' '
    self.initialize()

  def initialize(self):
    self.printers = []
    cols = col_count(self.rel)
    for i in range(0, cols):
       self.initialize_column(self.rel.column[i], i == 0, i == (cols - 1), cols)

  def escape_strings(self, flag):
     if flag:
        self.formatter["string_column"] = formatter_string
     else:
        self.formatter["string_column"] = formatter_string_noescape
     self.initialize()

  def entity_indexes(self, flag):
     self.print_entity_indexes = flag
     self.initialize()

  def output(self, f):
      rows = row_count(self.rel)
      for i in range(0, rows):
         result = []
         result = self.apply_printers(self.printers, i, result)
         f.write(self.delimiter.join(result))
         f.write('\n')

  def apply_printers(self, printers, i, result):
      for p in printers:
         if type(p) == list:
            result = self.apply_printers(p, i, result)
         else:
            result.append(p(i))
      return result

  def initialize_column(self, col, first, last, cols):
      self.printers.extend(self.get_printers(col, cols))
      #if not last:
      #   self.printers.append(print_separator)

  def get_printers(self, col, cols):
      funs = []
      if col.HasField('entity_column'):
         if col.entity_column.HasField('index_values'):
            if self.print_entity_indexes:
               col1 = col.entity_column.index_values
               fun1 = lambda i : print_index_cell(col1, i)
               max1 = self.max_width(col1, fun1)
               funs.append(lambda i : str.rjust(fun1(i), max1))
         if col.entity_column.HasField('refmode_values'):
            col2 = col.entity_column.refmode_values
            funs.append(self.get_printers(col2, cols))
      else:
         for t in column_fields():
            if col.HasField(t):
               actualc = getattr(col, t)
               formatter = self.formatter[t]
               if t == "decimal128_column":
                   fun2 = lambda i : formatter(actualc.negative[i], actualc.integral_digits[i],
                                               actualc.fraction_digits[i])
               elif t == "int128_column":
                   fun2 = lambda i : formatter(actualc.high[i], actualc.low[i])
               else:
                   fun2 = lambda i : formatter(actualc.values[i])
               if cols == 1:
                  # no justification needed if there's a single column
                  funs.append(fun2)
               else:
                  max2 = self.max_width(col, fun2)
                  funs.append(lambda i : str.ljust(fun2(i), max2))
      return funs

  def max_width(self, col, fun):
      maxwidth = 0
      rows = colrow_count(col)
      for i in range(0, rows):
         s = fun(i)
         if len(s) > maxwidth:
            maxwidth = len(s)
      return maxwidth

_EPOCH = datetime.datetime.utcfromtimestamp(0)

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

def get_cell_bool(col, i):
    return col.bool_column.values[i]

def get_cell_string(col, i):
    return col.string_column.values[i]

def get_cell_int64(col, i):
    return col.int64_column.values[i]

def get_cell_float64(col, i):
    return col.float64_column.values[i]

def get_cell_decimal128(col, i):
    negative = col.decimal128_column.negative[i]
    integral = col.decimal128_column.integral_digits[i]
    fraction = col.decimal128_column.fraction_digits[i]
    return serialized_decimal128_to_decimal(negative, integral, fraction)

def get_cell_datetime(col, i):
    return datetime.datetime.fromtimestamp(col.datetime_column.values[i], UTC())

def append_cell_bool(col, v):
    col.bool_column.values.append(v)

def append_cell_string(col, v):
    col.string_column.values.append(v)

def append_cell_int64(col, v):
    col.int64_column.values.append(v)

def append_cell_float64(col, v):
    col.float64_column.values.append(v)

def append_cell_decimal128(col, v):
    billion = 1000000000L;
    scaled = long(v.scaleb(18).to_integral_value())
    abs_scaled = abs(scaled)
    fraction = abs_scaled % (billion * billion)
    integral = abs((abs_scaled - fraction) / (billion * billion))
    negative = scaled < 0

    col.decimal128_column.negative.append(negative)
    col.decimal128_column.integral_digits.append(integral)
    col.decimal128_column.fraction_digits.append(fraction)

def append_cell_datetime(col, v):
    delta = v - _EPOCH
    seconds = int(delta.total_seconds())
    col.datetime_column.values.append(seconds)


# MB TODO Work in progress for writing better unit tests for updates
class SimpleRelation(object):

    def __init__(self):
        self._connectblox = None

    def _init_funs(self):
        self._getters = []
        self._appenders = []
        cols = col_count(self._connectblox)
        for i in range(0, cols):
            col = self._connectblox.column[i]
            self._getters.append(self._getter(col))
            self._appenders.append(self._appender(col))

    def _getter(self, col):
        if col.HasField("bool_column"):
            return lambda i: get_cell_bool(col, i)
        if col.HasField("int64_column"):
            return lambda i: get_cell_int64(col, i)
        if col.HasField("float64_column"):
            return lambda i: get_cell_float64(col, i)
        if col.HasField("string_column"):
            return lambda i: get_cell_string(col, i)
        if col.HasField("decimal128_column"):
            return lambda i: get_cell_decimal128(col, i)
        if col.HasField("datetime_column"):
            return lambda i: get_cell_datetime(col, i)

        raise NotImplementedError(col)

    def _appender(self, col):
        if col.HasField("bool_column"):
            return lambda v: append_cell_bool(col, v)
        if col.HasField("int64_column"):
            return lambda v: append_cell_int64(col, v)
        if col.HasField("float64_column"):
            return lambda v: append_cell_float64(col, v)
        if col.HasField("string_column"):
            return lambda v: append_cell_string(col, v)
        if col.HasField("decimal128_column"):
            return lambda v: append_cell_decimal128(col, v)
        if col.HasField("datetime_column"):
            return lambda v: append_cell_datetime(col, v)

        raise NotImplementedError(col)

    def _init_from_sample_row(self, t):
        rel = proto.Relation()

        for c in t:
            if isinstance(c, basestring):
                rel.column.add().string_column.Clear()
            elif isinstance(c, decimal.Decimal):
                col = rel.column.add()
                col.decimal128_column.Clear()
            elif isinstance(c, datetime.datetime):
                rel.column.add().datetime_column.Clear()
            elif type(c) == types.BooleanType:
                rel.column.add().bool_column.Clear()
            elif isinstance(c, (int, long)):
                rel.column.add().int64_column.Clear()
            elif isinstance(c, float):
                rel.column.add().float64_column.Clear()
            else:
                raise NotImplementedError(c)
        self.set_proto(rel)

    def __len__(self):
        return self.len()

    def __iter__(self):
        for i in xrange(0, self.len()):
            yield self.get(i)

    def len(self):
        if self._connectblox is None:
            return 0
        else:
            return row_count(self._connectblox)

    def __getitem__(self, i):
        return self.get(i)

    # Returns a tuple representation of this row, using native Python
    # data types.
    def get(self, i):
        cols = col_count(self._connectblox)
        t = []
        for j in range(0, cols):
            t.append(self.get_cell(i, j))
        return tuple(t)

    def get_cell(self, i, j):
        return self._getters[j](i)

    def extend(self, tuples):
        for t in tuples:
            self.append(t)

    def append(self, t):
        if self._connectblox is None:
            self._init_from_sample_row(t)

        cols = col_count(self._connectblox)

        if len(t) != cols:
            raise Exception("length of tuple and relation is not compatible")

        for j in range(0, cols):
           self._appenders[j](t[j])

    def get_proto(self):
        return self._connectblox

    def set_proto(self, rel):
        self._connectblox = rel

        self._init_funs()
        cols = col_count(self._connectblox)
        if len(self._appenders) != cols:
            raise Exception("Internal exception: length of appenders is incorrect")
        if len(self._getters) != cols:
            raise Exception("Internal exception: length of getters is incorrect")


class Relations(object):
    """The Relations class is merely a wrapper around a repeated
    blox.connect.Relation message in order to add convenience methods such as
    retreiving values from columns."""

    def __init__(self, relations):
        self.rel_hash = {}
        for relation in relations:
            self.rel_hash[relation.name] = relation

    def get_relation(self, name):
        """Returns the relations with the given name

        @param name:    the name of the relation
        @return:        a blox.connect.Relation or None if not found
        """
        return self.rel_hash.get(name)

    def get_column_values(self, name, col_idx):
        """Returns the relations with the given name

        @param name:    the name of the relation
        @param col_idx: the index of the column for which to retrieve values
        @return:        an array of values or an empty array if the relation
                        isn't found or col_idx is invalid
        """
        values = []
        rel = self.get_relation(name)
        if rel and len(rel.column) >= col_idx:
            col = rel.column[col_idx]
            if col.HasField('entity_column'):
                if col.entity_column.HasField('index_values'):
                    values = self._get_values(col.entity_column.index_values)
                if col.entity_column.HasField('refmode_values'):
                    values = self._get_values(col.entity_column.refmode_values)
            else:
                values = self._get_values(col)
        return values

    def get_values(self, name):
        """
        Returns the data of the given relation name as an array of rows

        ex: _[x,y] = z <- foo[x,y] = z.

        Will return the format of:
            [
                [x[0],y[0],z[0]],
                [x[1],y[1],z[1]],
                ...
            ]

        @param name:    the name of the relation
        @return:        an array of arrays where the inner arrays correspond to
                        a row of data
        """
        columns = []
        rel = self.get_relation(name)
        for col in rel.column:
            values = []
            if col.HasField('entity_column'):
                if col.entity_column.HasField('index_values'):
                    values = self._get_values(col.entity_column.index_values)
                if col.entity_column.HasField('refmode_values'):
                    values = self._get_values(col.entity_column.refmode_values)
            else:
                values = self._get_values(col)
            columns.append(values)

        return zip(*columns)

    def _get_values(self, col):
        """Helper method that gets the values based on the type of the given
        column.

        @param col:     a blox.connect.Column message
        @return:        an array of values or an empty array if no values exist
        """
        values = []
        for type in column_fields():
            if col.HasField(type):
                values = getattr(col, type).values
        return values
