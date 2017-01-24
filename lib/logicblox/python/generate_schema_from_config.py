import os
import argparse
import csv
from datetime import datetime
import clean_csvs

csv_filenames = [
    'CompositeAggs.csv',
    'CompositeSpreads.csv',
    'Dimensions.csv',
    'Hierarchies.csv',
    'Intersections.csv',
    'Levels.csv',
    'Measures.csv'
]


def mk_derivation_type(pred_name, der_type):
    return 'lang:derivationType[`%s] = "%s".' % (pred_name, der_type)

def mk_default_value(pred_name, value):
    return 'lang:defaultValue[`%s] = %s.' % (pred_name, value)


def process_config(config_dir, src_dir, csv_dir=None):
    if not os.path.exists(src_dir):
        os.makedirs(src_dir)

    logic_dir = src_dir + "/logiql/generated_schema"
    rules_dir = src_dir + "/rules"

    if not os.path.exists(logic_dir):
        os.makedirs(logic_dir)
    if not os.path.exists(rules_dir):
        os.makedirs(rules_dir)

    if csv_dir is not None:
        if not os.path.exists(csv_dir):
            os.makedirs(csv_dir)

        clean_csvs.clean_csvs(csv_filenames, config_dir, csv_dir)

        # if a csv_dir is specified it is b/c we are stripping the comments out
        # of the CSV files and putting the commentless CSV files into an output dir
        # Therefore, use the stripped csv_dir istead of the config dir
        config_dir = csv_dir

    # make project file
    make_project_file(src_dir)

    # convert Levels.csv
    all_levels = {}
    ordered_levels = []
    make_level_declarations(config_dir, logic_dir, all_levels, ordered_levels)

    # convert Hierarchies.csv to level map declerations
    make_levelmap_declarations(config_dir, logic_dir, all_levels, ordered_levels)

    # convert Measure.csv
    make_measure_declarations(config_dir, logic_dir)

    # generate measure rules for percent parent
    make_percent_parent_rules(config_dir, rules_dir)

def get_default_member_predicate(entity):
    return entity + "_default_member"

def make_ordered_level_sorting_rules(level, refmode_type, order_transform, transformed_type):
    level_refmode = level + ":id"    
    default_member = get_default_member_predicate(level)
    temp_idpred = "_" + level.replace(":", "_") + "_id"  #_level_id
    temp_seqpred = temp_idpred + "_seq"    #_level_id_seq
    level_first = level + "_first"
    level_next = level + "_next"
    level_last = level + "_last"
    level_index = level + "_index"
    level_transformed_id = ""
    
    if order_transform is None or order_transform == "" :
        id_type = refmode_type

        ordering_template = """
  /**************** Compute order for %(level)s **********************/
%(temp_idpred)s(id) <- 
  %(level_refmode)s(def,id), 
 !%(default_member)s(def).

%(temp_seqpred)s[i] = id -> int(i), %(id_type)s(id).
%(temp_seqpred)s[i] = id <- 
  seq<< >> 
    %(temp_idpred)s(id). 

%(level_first)s[] = ent <-
  %(temp_seqpred)s[0] = id,
  %(level_refmode)s(ent,id).

%(level_next)s[ent1] = ent2 <-
  %(temp_seqpred)s[i] = id1,
  %(temp_seqpred)s[i+1] = id2, 
  %(level_refmode)s[ent1] = id1,
  %(level_refmode)s[ent2] = id2.

%(level_index)s[ent] = index <- 
  %(temp_seqpred)s[index] = id,
  %(level_refmode)s[ent] = id.

%(level_last)s[] = ent <- 
  %(level)s(ent), 
  !%(default_member)s(ent),
  !%(level_next)s[ent] = _.

        """
    else:
        id_type = transformed_type
        level_transformed_id = level + "_transformed_id"
        ordering_template = """
  /**************** Compute order for %(level)s **********************/
%(order_transform)s[ent] = id -> %(level)s(ent), %(id_type)s(id).
  
%(temp_idpred)s(tid),
%(level_transformed_id)s[tid] = def <- 
 !%(default_member)s(def),
  %(order_transform)s(def, tid).

%(temp_seqpred)s[i] = id -> int(i), %(id_type)s(id).
%(temp_seqpred)s[i] = id <- 
  seq<< >> 
    %(temp_idpred)s(id). 

%(level_first)s[] = ent <-
  %(temp_seqpred)s[0] = id,
  %(level_transformed_id)s(id,ent).

%(level_next)s[ent1] = ent2 <-
  %(temp_seqpred)s[i] = id1,
  %(temp_seqpred)s[i+1] = id2,
  %(level_transformed_id)s[id1] = ent1,
  %(level_transformed_id)s[id2] = ent2.

%(level_index)s[ent] = index <- 
  %(temp_seqpred)s[index] = id,
  %(level_transformed_id)s[id] = ent.

%(level_last)s[] = ent <- 
  %(level)s(ent), 
  !%(default_member)s(ent),
  !%(level_next)s[ent] = _.

        """
        
    template_params = {'temp_idpred' : temp_idpred,
                       'temp_seqpred' : temp_seqpred,
                       'level_refmode' : level_refmode,
                       'id_type' : id_type,
                       'refmode_type': refmode_type,
                       'default_member' : default_member,
                       'level': level,
                       'level_first': level_first,
                       'level_next': level_next,
                       'level_last': level_last,
                       'level_index': level_index,
                       'order_transform': order_transform,
                       'level_transformed_id': level_transformed_id
                       }
    
    return ordering_template % template_params

def make_percent_parent_rules(config_dir, rules_dir):
    rules_file = open(rules_dir + "/percent_parent_rules.rules", 'w')
    insert_do_not_edit(rules_file)

    # Intersection,Order,Dimension,Level
    intersection_dict = {}
    with open(config_dir + "/Intersections.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            intersection_name = row["Intersection"].strip()
            order = int(row["Order"].strip())
            dimension_name = row["Dimension"].strip()
            level_name = row["Level"].strip()

            if intersection_name in intersection_dict:
                ilist = intersection_dict[intersection_name]
            else:
                ilist = []
                intersection_dict[intersection_name] = ilist

            ilist.insert(order, [dimension_name, level_name])

    with open(config_dir + "/Measures.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            measure_name = row["Measure"].strip()
            intersection = row["Intersection"].strip()
            percent_base = row["PercentBase"].strip()
            percent_parent_dim = row["PercentParentDimension"].strip()
            default_value = row["DefaultValue"].strip()

            if len(percent_base) > 0:
                dim_level_list = intersection_dict[intersection]

                ppargs = ""
                ppargindex = 0
                baseargs = ""
                parentargs = ""
                argsindex = 0

                for dim_level in dim_level_list:
                    dimension = dim_level[0]

                    if ppargindex > 0:
                        ppargs += ", "
                    if argsindex > 0:
                        baseargs += ", "
                        parentargs += ", "

                    if dimension == percent_parent_dim:
                        argname = "x" + str(ppargindex) + "_child"
                        ppargs += argname
                        ppargs += ", "
                        baseargs += argname
                        ppargindex += 1

                        argname = "x" + str(ppargindex) + "_parent"
                        ppargs += argname
                        parentargs += argname

                        ppargindex += 1
                        argsindex += 1

                    else:
                        argname = "x" + str(ppargindex)
                        ppargs += argname
                        baseargs += argname
                        parentargs += argname
                        ppargindex += 1
                        argsindex += 1

                if not default_value:
                    formula_template = """
                          %(measure_name)s[%(ppargs)s] = %(percent_base)s[%(baseargs)s] / %(percent_base)s[%(parentargs)s].\n
                    """
                else:
                    formula_template = """
                          %(measure_name)s[%(ppargs)s] = v where \n
                             %(percent_base)s[%(baseargs)s] = num and num != %(default_value)s \n
                             and %(percent_base)s[%(parentargs)s] = denom and denom != %(default_value)s \n
                             and v = num / denom .\n """

                template_params = { 'measure_name': measure_name,
                                    'ppargs': ppargs,
                                    'percent_base': percent_base,
                                    'baseargs': baseargs,
                                    'parentargs': parentargs,
                                    'default_value': default_value }
                formula = formula_template % template_params
    
                rule = "rule \"" + measure_name + "\" { \n"
                rule += "   formula \"" + measure_name + "\" { \n"
                rule += formula
                rule += "   }\n"
                rule += "}"
                                
                rules_file.write(rule + "\n")

    rules_file.close()

def make_measure_declarations(config_dir, logic_dir, measures_to_process=None):
    measureout_file = open(logic_dir + "/measures.logic", 'w')
    insert_do_not_edit(measureout_file)

    # read in intersection info first.
    # we need level information as well to get dimension.

    level_to_dim = {}
    intersection_dict = {}
    dim_set = set()

    with open(config_dir + "/Dimensions.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            dim_set.add(row["Dimension"].strip())

    with open(config_dir + "/Levels.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            level_to_dim[row["Level"].strip()] = row["Dimension"].strip()
            # every level is an intersection
            intersection_name = row["Dimension"].strip() + ":" + row["Level"].strip()
            intersection_dict[intersection_name] = [[row["Dimension"].strip(), row["Level"].strip()]]

    # Intersection,Order,Dimension,Level
    with open(config_dir + "/Intersections.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            intersection_name = row["Intersection"].strip()
            order = int(row["Order"].strip())
            dimension_name = row["Dimension"].strip()
            level_name = row["Level"].strip()

            # check Dimension exists
            if not (dimension_name in dim_set):
                raise Exception("Warning: for dimension " + dimension_name + ", dimension not found in Dimensions.csv")
            
            # check Level exists
            if not (level_name in level_to_dim):
                raise Exception("Warning: for level " + level_name + ", level not found in Levels.csv")

            if intersection_name in intersection_dict:
                ilist = intersection_dict[intersection_name]
            else:
                ilist = []
                intersection_dict[intersection_name] = ilist

            ilist.insert(order, [dimension_name, level_name])

    # collect possible spreads
    spreads_empty = ["none", ""]
    spreads_recalc = ["recalc", "percentparent"]
    spreads_normal = ["even", "ratio", "ratioEven", "delta", "replicate"]
    spreads_defined = ["and", "or", "first", "last", "bop", "bopambig", "eop"]
    spreads_composite_set = set([])
    with open(config_dir + "/CompositeSpreads.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            spreads_composite_set.add(row["Name"].strip())
    spreads_composite = list(spreads_composite_set)
    spreads_all = spreads_empty + spreads_recalc + spreads_normal + spreads_defined + spreads_composite

    with open(config_dir + "/Measures.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            measure_name = row["Measure"].strip()
            intersection = row["Intersection"].strip()
            value_datatype = row["DataType"].strip()
            default_value = row["DefaultValue"].strip()
            percent_base = row["PercentBase"].strip()
            extensional = False
            default_agg = row["DefaultAgg"].strip()
            default_spread = row["DefaultSpread"].strip()
            spread_by_metric = row["SpreadByMetric"].strip()

            if measures_to_process and measure_name not in measures_to_process:
                continue

            if "DerivationType" in row:
                extensional = (row["DerivationType"].strip().lower() == 'extensional')

            # do not generate for percent parent measure.
            # NOTE: those do not have the signature you think they do
            # so they really need to be skipped for now
            if len(percent_base) > 0:
                continue

            types = []
            args = []

            # check DefaultSpread
            if not (default_spread in spreads_all):
                raise Exception("Warning: for measure " + measure_name + ", DefaultSpread is " + default_spread + " which is invalid")

            # a recalc can only have a non-trivial DefaultSpread
            if (default_agg in ["recalc","percentParent"]) and (not (default_spread in ["", "none", "recalc", "percentParent"])):
                raise Exception("Warning: for measure " + measure_name + ", DefaultAgg is " + default_agg + ", and DefaultSpread is " + default_spread + " but should be empty")

            # SpreadByMetric is only valid on ratio/ratioEven DefaultSpread
            if spread_by_metric != "" and (not (default_spread == "ratio" or default_spread == "ratioEven" )):
                raise Exception("Warning: for measure " + measure_name + ", SpreadByMetric is " + spread_by_metric + ", and DefaultSpread is " + default_spread + ", but should be ratio or ratioEven")

            if len(intersection) > 0:
                dim_level_list = intersection_dict[intersection]

                qualified_levels = ['%s:%s' % (l[0], l[1]) for l in dim_level_list]
                types = qualified_levels
                args = ['x%d' % i for i in range(len(qualified_levels))]

            types = ['%s(%s)' % (t, v) for t, v in zip(types + [value_datatype], args + ['v'])]

            decl = measure_name + "[%s] = v -> %s." % (', '.join(args), ', '.join(types))
            measureout_file.write(decl + "\n")

            if default_value:
                measureout_file.write(mk_default_value(measure_name, default_value) + '\n')

            if extensional:
                measureout_file.write(mk_derivation_type(measure_name, 'Extensional') + '\n')

    measureout_file.close()


def make_level_declarations(config_dir, logic_dir, all_levels, ordered_levels):
    # for level file, create <src_dir>/levels.logic
    levelout_filename = get_level_schema_filename(logic_dir)
    level_file = config_dir + "/Levels.csv"

    # Levels.csv headers
    # Level,Label,Dimension,ElementType,IsOrdered,OrderAttribute,OrderTransform,TransformedType
    #
    # For each level, generate
    #   <entity>(x), <refmode>(x:id) -> <elementType>(id).
    #   <entity_label>[x] = l -> <elementType>(x), string(l).
    # where
    #   <entity> = <dimension>:<Level>
    #   <refmode> = <dimension>:<Level>:id
    #   <entity_label> = <entity>:label
    levelout_file = open(levelout_filename, 'w')
    insert_do_not_edit(levelout_file)
    with open(level_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            level = row["Level"].strip()
            dimension = row["Dimension"].strip()
            element_type = get_4x_type(row["ElementType"].strip())
            is_ordered = row["IsOrdered"].strip()
            order_transform = row["OrderTransform"].strip()
            transformed_type = row["TransformedType"].strip()

            entity_name = dimension + ":" + level
            refmode_name = entity_name + ":id"
            entity_label_name = entity_name + ":label"

            levelout_file.write(mk_derivation_type(entity_name, 'Extensional') + '\n')
            levelout_file.write(entity_name + "(x), " + refmode_name + "(x:id) -> " + element_type + "(id).\n")
            levelout_file.write(entity_label_name + "[x] = y -> " + entity_name + "(x), string(y).\n")
            levelout_file.write(mk_derivation_type(entity_label_name, 'Extensional') + '\n')

            all_levels[entity_name] = element_type

            levelout_file.write(
                get_default_member_predicate(entity_name) + "(x) -> " + entity_name + "(x).\n")

            if is_ordered == 'true':
                # levelout_file.write("lang:ordered(`" + entity_name + ").\n")
                ordered_levels.append(entity_name)

                first_name = entity_name + "_first"
                last_name = entity_name + "_last"
                next_name = entity_name + "_next"
                index_name = entity_name + "_index"
                offset_name = entity_name + "_offset"
                tdxoffset_name = entity_name + "_tdxoffset"
                lt_name = entity_name + ":lt_2"

                levelout_file.write(first_name + "[] = x -> " + entity_name + "(x).\n")
                levelout_file.write(last_name + "[] = x -> " + entity_name + "(x).\n")
                levelout_file.write(next_name + "[x] = y -> " + entity_name + "(x), " + entity_name + "(y).\n")
                levelout_file.write(index_name + "[x] = i -> " + entity_name + "(x), int(i).\n")
                levelout_file.write(offset_name + "[x,y] = o -> " + entity_name + "(x), " + entity_name + "(y), int(o).\n")
                levelout_file.write(offset_name + "[x,y] = " + index_name + "[y] - " + index_name + "[x].\n")
                levelout_file.write(mk_derivation_type(offset_name, 'Derived') + '\n')
                levelout_file.write(lt_name + "(x,y) <- " + index_name + "[x] < " + index_name + "[y].\n")
                levelout_file.write(lt_name + "(x,y) -> " + entity_name + "(x), " + entity_name + "(y).\n")
                levelout_file.write(mk_derivation_type(lt_name, 'Derived') + '\n')

                levelout_file.write(tdxoffset_name + "(x, i) -> " + entity_name + "(x), int(i).\n")

                # generate sorting logic
                levelout_file.write(make_ordered_level_sorting_rules(entity_name, element_type, order_transform, transformed_type))

    levelout_file.close()


def get_default_refmode_value(refmode_type):
    refmode_value = None

    if refmode_type == "string":
        refmode_value = "\"zzz_____default_level_member\""
    elif refmode_type == "int":
        refmode_value = "-1"
    elif refmode_type == "float":
        refmode_value = "-1f"
    elif refmode_type == "decimal":
        refmode_value = "-1d"
    #  a boolean level does not have a default member.

    return refmode_value


def make_orphan_decls(orphan_decls_file):
    orphan_decls_file.write(
        "// user-defined orphan parent name \n"
        "orphan_parent_name[level_name] = parent_name -> string(level_name), string(parent_name).\n"
        "// default orphan parent name  : none \n"
        "orphan_parent_default_name[] = n -> string(n).\n"
        "orphan_parent_default_name[] = \"~ (none) ~\".\n"
        "orphan_parent_name[level_name] = n -> string(level_name), string(n).\n\n"
        "// real default level member name\n"
        "real_default_level_member_name[level_name] = member_name -> string(level_name), string(member_name). \n"
        "real_default_level_member_name[level_name] = orphan_parent_name[level_name]. \n"
        "real_default_level_member_name[qualified_lname] = default_name <- \n"
        "  lb:web:measure:Dimension_level(dim,level), \n"
        "  lb:web:measure:Dimension_name(dim, dimname), \n"
        "  lb:web:measure:Dimension:Level_name(level, level_name), \n"
        "  qualified_lname = dimname + \":\" + level_name, \n"
        "  !orphan_parent_name[qualified_lname] = _,\n"
        "  orphan_parent_default_name[] = default_name.\n\n")

def make_orphan_logic(orphan_file, from_entity, to_entity, to_refmode_type, mappred):
    to_entity_id = to_entity + ":id"
    to_entity_label = to_entity + ":label"
            
    # declare the predicate keeping count of how many orphan children a parent has
    # this is the predicate we use to determine whether a default member (~none~) would
    # be created.
    # +mappred_count[] = n <-
    #  agg<< n = count() >>
    #    from_entity(from),
    #    ! mappred(from, _).
    mappred_count = "_" + mappred + "_count"
    orphan_file.write(mappred_count + "[] = n -> int(n).\n")
    orphan_file.write(
        "+" + mappred_count + "[] = n <- \n" +
        "  agg<< n = count() >> \n" +
        "    " + from_entity + "(from),\n" +
        "    !" + mappred + "(from, _).\n")

    # if mappred_count is not existent, then add retraction request.
    # if mappred_count > 0, then add addition request.
    #
    # +retraction_pred(def) <-
    #   !mappred_count[] = _
    #   to_entity_id(def, def_refmode).
    # 
    # +addition_pred(def) <-
    #   mappred_count[] > 0,
    #   to_entity_id(def, def_refmode).
    retraction_pred = "_" + to_entity + "_retract_default"
    addition_pred = "_" + to_entity + "_add_default"
    to_refmode_value = get_default_refmode_value(to_refmode_type)
    to_default_member_pred = get_default_member_predicate(to_entity)
            
    orphan_file.write(
        retraction_pred + "(def) -> " + to_entity + "(def).\n" +
        addition_pred + "(def) -> " + to_entity + "(def).\n" +
        "+" + retraction_pred + "(def) <- \n" +
        "   !" + mappred_count + "[] = _, \n" +
        "   " + to_entity_id + "(def, def_refmode), \n" +
        "   def_refmode = " + to_refmode_value + ".\n" +
        "+" + addition_pred + "(def) <- \n" +
        "   " + mappred_count + "[] > 0, \n" +
        "   " + to_entity_id + "(def, def_refmode), \n" +
        "   def_refmode = " + to_refmode_value + ".\n")                

    # +to_default_member_pred(def),
    # +to_entity(def), +to_entity_id(def, def_refmode),
    # +to_entity_label(def, def_label),
    # +addition_pred(def) <-
    #   +to_entity(to),
    #   !+mappred(to, _).
    #
    # -to_default_member_pred(def) <-
    #   retraction_pred(def),
    #   !addition_pred(def).

    orphan_file.write(
        "+" + to_default_member_pred + "(def),\n"
        "+" + to_entity + "(def), \n"
        "+" + to_entity_id + "(def, def_refmode), \n"
        "+" + to_entity_label + "(def, def_label), \n"
        "+" + addition_pred + "(def) <- \n"
        "   " + from_entity + "(from),\n"
        "   !" + mappred + "(from, _), \n"
        "   real_default_level_member_name[\"" + to_entity + "\"] = def_label, \n"
        "   def_refmode = " + to_refmode_value + ".\n")

    orphan_file.write(
        "-" + to_default_member_pred + "(def), \n"
        "-" + to_entity + "(def) <- \n"
        "   !" + addition_pred + "(def), \n " +
        "   " + retraction_pred + "(def).\n")
            

def make_levelmap_declarations(config_dir, logic_dir, all_levels, ordered_levels):
    # for LevelMap and LevelMap_fromLevel files, create <src_dir>/levelmap.logic
    levelmap_filename = logic_dir + "/levelmaps.logic"

    # create <src_dir>/fix_orphan_levels.logic
    # this file contains logic that will map all orphan levels to a (none) level in the parent.
    # the exact name of the (none) level would be configurable.
    orphan_filename = logic_dir + "/fix_orphan_levels.logic"
    orphan_decls_filename = logic_dir + "/fix_orphan_levels_decls.logic"

    # declare logic to set level (none) names
    orphan_file = open(orphan_filename, 'w')
    orphan_decls_file = open(orphan_decls_filename, 'w')

    make_orphan_decls(orphan_decls_file)

    # Hierarchies.csv headers
    #   Hierarchy,Dimension,IsDefault,FromLevel,ToLevel,Index,HasFirst,HasLast
    #
    # for each pair of (FromLevel, ToLevel), create a mapping predicate
    #   <mapping_pred>[from] = to -> <from_level_type>(from), <to_level_type>(to).
    # where
    #   <mapping_pred> = <dimension>:<fromLevels>:<toLevel>
    # and from_level_type and to_level_type are those created for those levels

    levelmap_file = open(levelmap_filename, 'w')
    insert_do_not_edit(levelmap_file)

    ordered_levels_set = set(ordered_levels)
    with open(config_dir + "/Hierarchies.csv", 'rb') as f:
        reader = csv.DictReader(f)
        levelmap_set = set()
        for row in reader:
            hierarcy_name = row["Hierarchy"].strip()
            dimension_name = row["Dimension"].strip()
            from_level_name = row["FromLevel"].strip()
            to_level_name = row["ToLevel"].strip()

            levelmap_key = hierarcy_name + dimension_name + from_level_name + to_level_name

            if (levelmap_key in levelmap_set):
                raise Exception("Warning: Level mapping duplicated for Hierarchy %s, Dimension %s, FromLevel %s, and toLevel %s" % (hierarcy_name,dimension_name,from_level_name,to_level_name))
            else:
                levelmap_set.add(levelmap_key)

            to_level_fixed = to_level_name[0].lower() + to_level_name[1:]
            mappred = dimension_name + ":" + from_level_name + ":" + to_level_fixed
            mappred_derived = dimension_name + ":" + from_level_name + ":" + to_level_fixed + "_derived"
            from_entity = dimension_name + ":" + from_level_name
            from_entity_id = from_entity + ":id"
            from_refmode_type = all_levels[from_entity]
            to_entity = dimension_name + ":" + to_level_name
            to_refmode_type = all_levels[to_entity]
            to_refmode_value = get_default_refmode_value(to_refmode_type)
            to_entity_id = to_entity + ":id"
            to_entity_label = to_entity + ":label"

            # generate orphan logic for this mapping
            make_orphan_logic(orphan_file, from_entity, to_entity, to_refmode_type, mappred)

            levelmap_file.write("/********** Mapping declarations for %s to %s ***************/" % (from_entity, to_entity))
            # declare the mapping predicate.
            levelmap_file.write(mappred + "[from] = to -> " + from_entity + "(from), " + to_entity + "(to).\n")
            levelmap_file.write(mk_derivation_type(mappred, "Extensional") + '\n')
            # declare the derived mapping predicate.
            levelmap_file.write(mappred_derived + "[from] = to -> " + from_entity + "(from), " + to_entity + "(to).\n")

            # declare default_member predicate for the to_entity
            to_default_member_pred = get_default_member_predicate(to_entity)

            # rule from mappred to mappred_derived
            levelmap_file.write(mappred_derived + "[from] = to <- " + mappred + "[from] = to.\n")
            levelmap_file.write(
                mappred_derived + "[from] = parent <- " +
                "  " + from_entity + "(from), \n" +
                "  !" + mappred + "[from] = _, \n" +
                "  " + to_entity_id + "[parent] = " + to_refmode_value + ".\n")

            # map the default member of the from level to the default member in to level.
            levelmap_file.write(
                mappred_derived + "[from] = to <- \n"
                "   " + from_entity + ":id(from, " + get_default_refmode_value(from_refmode_type) + "), \n"
                "   " + to_entity_id + "(to, " + to_refmode_value + ").\n")

            # see whether we need to generate mapping_first, mapping_last, and mapping_next
            if to_entity in ordered_levels_set and from_entity in ordered_levels_set:
                levelmap_file.write("/********** Sorting for mapping from %s to %s ***************/" % (from_entity, to_entity))
                from_level_fixed = from_level_name[0].lower() + from_level_name[1:]

                for nth in ["first", "last"]:
                    # dimension_name:from_level_name:to_level_fixed_{first,last}
                    map_nth = mappred + "_" + nth
                    levelmap_file.write(map_nth + "[from] = to -> " + from_entity + "(from), " + to_entity + "(to).\n")

                    map_derived_nth = mappred_derived + "_" + nth
                    levelmap_file.write(map_derived_nth + "[from] = to -> " + from_entity + "(from), " + to_entity + "(to).\n")

                    levelmap_file.write(map_derived_nth + "[from] = to <- " + map_nth + "[from] = to.\n")


                reverse_map = dimension_name + ":" + to_level_name + ":" + from_level_fixed
                reverse_map_next = reverse_map + "_next"
                reverse_map_derived_next = reverse_map + "_derived_next"
                levelmap_file.write(reverse_map_next + "[to, from1] = from2 -> " +
                                    from_entity + "(from1), " + from_entity + "(from2), " + to_entity + "(to).\n")
                levelmap_file.write(reverse_map_derived_next + "[to, from1] = from2 -> " +
                                    from_entity + "(from1), " + from_entity + "(from2), " + to_entity + "(to).\n")
                levelmap_file.write(reverse_map_derived_next + "[to, from1] = from2 <- " +
                                    reverse_map_next + "[to, from1] = from2.\n")

                levelmap_file.write(make_mapped_order_logic(from_entity, to_entity, mappred))

    orphan_file.close()
    orphan_decls_file.close()
    levelmap_file.close()

def make_mapped_order_logic(from_entity,to_entity,mappred):
    return ''.join([make_mapped_first_logic(from_entity,to_entity,mappred),
                    make_mapped_last_logic(from_entity,to_entity,mappred),
                    make_mapped_next_logic(from_entity,mappred)])
    
def make_mapped_first_logic(from_entity,to_entity,mappred):
    return make_mapped_first_last_logic(from_entity,to_entity,mappred,mappred +"_first","min")

def make_mapped_last_logic(from_entity,to_entity,mappred):
    return make_mapped_first_last_logic(from_entity,to_entity,mappred,mappred + "_last","max")

def make_mapped_first_last_logic(from_entity, to_entity, mappred, destpred, aggmethod):
    # mappred_index[to] = firstindex -> to_entity(to), int(firstindex).
    # mappred_index[to] = firstindex <- 
    #   agg<< firstindex = min(fromindex) >>   or max
    #     mappred[from] = to,
    #     from_entity_index[from] = fromindex
    # mappred[from] = to <-
    #   mappred_index[to] = firstindex,
    #   from_entity_index[from] = firstindex.
    destpred_index = destpred + "_index"
    from_entity_index = from_entity + "_index"

    template = """
%(destpred_index)s[to] = firstindex -> %(to_entity)s(to), int(firstindex).
%(destpred_index)s[to] = firstindex <-
   agg<< firstindex = %(aggmethod)s(fromindex) >>
     %(mappred)s[from] = to,
     %(from_entity_index)s[from] = fromindex.
%(destpred)s[from] = to <-
   %(destpred_index)s[to] = firstindex,
   %(from_entity_index)s[from] = firstindex.
    """
    
    params = {'destpred_index': destpred_index,
              'mappred': mappred,
              'destpred': destpred,
              'to_entity': to_entity,
              'from_entity_index': from_entity_index,
              'aggmethod' : aggmethod}

    return template % params

def make_mapped_next_logic(from_entity,mappred):
      
    # mappred_next[to,from1]=from2 <-
    #   mappred[from1]=to,
    #   mappred[from2] = to,
    #   from_entity_index[from1] = i,
    #   from_entity_index[from2] = i+1.

    mappred_next = mappred + "_next"
    from_entity_index = from_entity + "_index"

    template = """
%(mappred_next)s[to,from1] = from2 <-
  %(mappred)s[from1] = to,
  %(mappred)s[from2] = to,
  %(from_entity_index)s[from1] = i,
  %(from_entity_index)s[from2] = i+1.
    """

    params = {'mappred_next': mappred_next,
              'mappred': mappred,
              'from_entity_index': from_entity_index }

    return template % params

def make_project_file(src_dir):
    project_filename = src_dir + "/logiql/generated_schema.project"
    project_file = open(project_filename, 'w')
    insert_do_not_edit(project_file)
    project_file.write("generated_schema,projectname\n\n")
    project_file.write("lb_measure_service, library\n\n")
    project_file.write("generated_schema/levels.logic,active\n")
    project_file.write("generated_schema/fix_orphan_levels_decls.logic,active\n")
    project_file.write("generated_schema/levelmaps.logic,active\n")
    project_file.write("generated_schema/fix_orphan_levels.logic,inactive\n")
    project_file.write("generated_schema/measures.logic,active\n")
    project_file.close()


def insert_do_not_edit(f):
    f.write("// GENERATED FILE. DO NOT EDIT\n")
    current_time = datetime.now()
    f.write("// GENERATED ON: " + str(current_time) + "\n\n")


def get_level_schema_filename(src_dir):
    return src_dir + "/levels.logic"


def get_4x_type(element_type):
    if element_type.startswith("float"):
        return "float"
    elif element_type.startswith("int"):
        return "int"
    elif element_type.startswith("uint"):
        return "int"
    elif element_type.startswith("decimal"):
        return "decimal"
    return element_type


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'config_dir',
        help='Directory containing csv configuration files (Measures.csv, Levels.csv, etc')
    parser.add_argument(
        'src_dir',
        help='Directory to place the resulting logiql files')
    parser.add_argument(
        'csv_dir',
        nargs="?",
        help='Temporary directory where clean csvs will be placed before they are processed')
    args = parser.parse_args()

    config_dir = args.config_dir
    src_dir = args.src_dir
    csv_dir = args.csv_dir

    process_config(config_dir, src_dir, csv_dir)

if __name__ == '__main__':
    main()
