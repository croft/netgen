#
# This file defines generic measure expression term constructors for
#      use in defining tests.
# 

import sys
import os
import unittest

sys.path.insert(0, '%s/lib/python' % os.environ.get('LOGICBLOX_HOME'))
sys.path.insert(0, '%s/lib/python' % os.environ.get('LB_WEBSERVER_HOME'))

import lb.web.testcase
import lb.web.service
import lb.web.admin

#
# Request builders
#

def query(test_case, report_name):
  req = test_case.client.dynamic_request()
  req.kind = 1 # QUERY
  req.query_request.report_name = report_name
  return req
  
def install(req, *measures):
  req.kind = 2 # INSTALL
  for measure in measures:
      req.install_request.measure_expr.add().MergeFrom(measure)
  return req

def installFromString(req, *measureStrings):
  req.kind = 2 # INSTALL
  for measureString in measureStrings:
      req.install_request.measure_text.append(measureString)
  return req

def bind(req, *bindings):
  # TODO - this is not working yet
  req.kind = 3 # BINDING
  for binding in bindings:
      req.binding_request.add().MergeFrom(binding)
  return req
    
    #
    # Generic term constructors
    #

def key_request(test_case,dim,hier,level,attribute):
  key_req = test_case.client.dynamic_message("lb.web.measure.KeyRequest")
  key_req.qualified_level.CopyFrom(qualifiedLevel(test_case, dim, hier, level))
  key_req.attribute = attribute
  return key_req
  
def baseMeasure(test_case, measure_name):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.metric.name = measure_name

  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  return expr

def attribute(test_case, dimension_name, hierarchy_name, level_name, attribute_name):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.attribute.qualified_level.dimension = dimension_name
  expr.attribute.qualified_level.hierarchy = hierarchy_name
  expr.attribute.qualified_level.level = level_name
  expr.attribute.attribute = attribute_name
  expr.kind = 5 # query_pb2.MeasureExpr.ATTRIBUTE
  return expr

def aggregation(test_case, method, group_list, subExpr):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 2 # query_pb2.MeasureExpr.AGGREGATION
  expr.aggregation.method = method
  for grp in group_list:
    expr.aggregation.grouping.add().MergeFrom(grp)
  expr.aggregation.expr.CopyFrom(subExpr)
  return expr

def filter(test_case, subExpr, cond_list):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  sub_expr = filterBody(test_case, subExpr, cond_list) 
  if sub_expr.DESCRIPTOR.name == "FilterExpr":
    expr.kind = 3 # query_pb2.MeasureExpr.FILTER
    expr.filter.CopyFrom(sub_expr)
  else:   
    expr.kind = 9 # query_pb2.MeasureExpr.DICE
    expr.dice.CopyFrom(sub_expr)
  return expr

def qualifiedLevel(test_case,dim,hier,level):
  qualifiedLevel = test_case.client.dynamic_message("lb.web.measure.QualifiedLevel")
  qualifiedLevel.dimension = dim
  qualifiedLevel.hierarchy = hier
  qualifiedLevel.level = level
  return qualifiedLevel

def union(test_case, exprList):
  comp = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  comp.kind = 4 # query_pb2.MeasureExpr.COMPOSITE
  comp.composite.kind = 2 # UNION
  for expr in exprList:
    comp.composite.expr.add().MergeFrom(expr)
  return comp

def intersect(test_case, exprList):
  comp = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  comp.kind = 4 # query_pb2.MeasureExpr.COMPOSITE
  comp.composite.kind = 1 # INTERSECTION
  for expr in exprList:
    comp.composite.expr.add().MergeFrom(expr)
  return comp

def bindingRequest(test_case, expr, response_pred, request_pred):
  binding = test_case.client.dynamic_message("lb.web.measure.BindingRequest")
  binding.expr.MergeFrom( expr )
  binding.response_binding_predicate = response_pred
  binding.request_binding_predicate = request_pred
  return binding

#
# Agg grouping constructors
#
def all_grouping(test_case, dimension):
  grp = test_case.client.dynamic_message("lb.web.measure.AggExpr.Grouping")
  grp.kind = 2 # query_pb2.Grouping.ALL
  grp.dimension = dimension
  return grp

def map_grouping(test_case, dimension, level, hier=None):
  grp = test_case.client.dynamic_message("lb.web.measure.AggExpr.Grouping")
  grp.kind = 3 # query_pb3.Grouping.MAP
  grp.dimension = dimension
  grp.level = level
  if hier is not None:
    grp.hierarchy = hier
  return grp

def no_grouping(test_case, dimension):
  grp = test_case.client.dynamic_message("lb.web.measure.AggExpr.Grouping")
  grp.kind = 1 # query_pb3.Grouping.NO_GROUPING
  grp.dimension = dimension
  return grp

def multi_dim_grouping(test_case, dimension, mapping):
  grp = test_case.client.dynamic_message("lb.web.measure.AggExpr.Grouping")
  grp.kind = 4 # query_pb2.Grouping.MULTI_MAP
  grp.dimension = dimension
  grp.multi_dim_map = mapping
  return grp

def by(test_case, comp_list):
  return comp_list

def where(test_case, expr, comp_list):
  if not comp_list:
    return expr
  else:  
    mExpr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
    mExpr.filter.expr.CopyFrom(expr)
    for comp in comp_list:
      mExpr.filter.comparison.add().MergeFrom(comp)
    mExpr.kind = 3 # query_pb2.MeasureExpr.FILTER
    return mExpr

def whereEither(test_case, expr, comp_list):
  if not comp_list:
    return expr
  else:
    mExpr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
    mExpr.filter.expr.CopyFrom(expr)
    mExpr.filter.is_disjunction = True
    for comp in comp_list:
      mExpr.filter.comparison.add().MergeFrom(comp)
    mExpr.kind = 3 # query_pb2.MeasureExpr.FILTER
    return mExpr

def comparison(test_case, op, term):
  comp = test_case.client.dynamic_message("lb.web.measure.Comparison")
  comp.op = op
  comp.term.MergeFrom(term)
  return comp

def int_comparison(test_case, op, term):
  comp = test_case.client.dynamic_message("lb.web.measure.Comparison")
  comp.op = op
  comp.term.kind = 2
  comp.term.constant.int_constant = term
  return comp

def float_comparison(test_case, op, term):
  comp = test_case.client.dynamic_message("lb.web.measure.Comparison")
  comp.op = op
  comp.term.kind = 2
  comp.term.constant.float_constant = term
  return comp

def string_comparison(test_case, op, term):
  comp = test_case.client.dynamic_message("lb.web.measure.Comparison")
  comp.op = op
  comp.term.kind = 2
  comp.term.constant.string_constant = term
  return comp

def param_value(test_case, name):
  term = test_case.client.dynamic_message("lb.web.measure.Term")
  term.kind = 1
  term.param.name = name 
  term.param.type = 1 
  return term

def string_value(test_case, constant):
  term = test_case.client.dynamic_message("lb.web.measure.Term")
  term.kind = 2
  term.constant.string_constant = constant
  return term


#
# Agg method constants
#
def no_agg_method():
  return 2 # query_pb2.Aggregation.NO_AGGREGATION

def total_method():
  return 4 # query_pb2.Aggregation.TOTAL

def min_method():
  return 6 # query_pb2.Aggregation.MIN

def max_method():
  return 7 # query_pb2.Aggregation.MAX

def count_method():
  return 8 # query_pb2.Aggregation.COUNT

def mode_method():
  return 17 # query_pb2.Aggregation.MODE

def count_distinct_method():
  return 18 # query_pb2.Aggregation.COUNT_DISTINCT

#
# Comparison constants
#
def EQUALS():
  return 1 # query_pb2.ComparisonOp.EQUALS

def NOT_EQUALS():
  return 2 # query_pb2.ComparisonOp.NOT_EQUALS

def LESS_THAN():
  return 3 # query_pb2.ComparisonOp.LESS_THAN

def LESS_OR_EQUALS():
  return 4 # query_pb2.ComparisonOp.LESS_OR_EQUALS

def GREATER_THAN():
  return 5 # query_pb2.ComparisonOp.GREATER_THAN

def GREATER_OR_EQUALS():
  return 6 # query_pb2.ComparisonOp.GREATER_OR_EQUALS

#
# Custom queries
#

def distr_query(test_case):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  expr.metric.name = "Distr"
  return expr

def distr_store_query(test_case):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  expr.metric.name = "DistrStore"
  return expr

def user_query(test_case):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  expr.metric.name = "UserAuth"
  return expr

def vendor_query(test_case):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  expr.metric.name = "VendorAuth"
  return expr

def super_user_query(test_case):
  expr = test_case.client.dynamic_message("lb.web.measure.MeasureExpr")
  expr.kind = 1 # query_pb2.MeasureExpr.MEASURE
  expr.metric.name = "SuperUserAuth"
  return expr


#
# Internal implementation methods
#

def filterBody(test_case, expr, cond_list, disj=False):
  filter = test_case.client.dynamic_message("lb.web.measure.FilterExpr")
  dice = test_case.client.dynamic_message("lb.web.measure.DiceExpr")
  needs_filter = False
  needs_dice = False
  for cond in cond_list:
    #import pdb;pdb.set_trace()
    if isinstance(cond, list):
      for innerCond in cond:
        filter.comparison.add().MergeFrom(innerCond)
        needs_filter = True
    elif cond.DESCRIPTOR.name == "MeasureExpr":
      dice.dicer.add().MergeFrom(cond)
      needs_dice = True
    elif cond.DESCRIPTOR.name == "Comparison":
      filter.comparison.add().MergeFrom(cond)
      needs_filter = True
  if needs_dice and needs_filter:
    dice.expr.CopyFrom(expr)
    filter.expr.kind = 9 
    filter.expr.dice.CopyFrom(dice)
    if(disj):
      filter.is_disjunction = True  
    return filter  
  elif needs_dice:
    dice.expr.CopyFrom(expr)
    if(disj):
      dice.is_disjunction = True  
    return dice
  elif needs_filter:
    filter.expr.CopyFrom(expr)
    if(disj):
      filter.is_disjunction = True  
    return filter  
