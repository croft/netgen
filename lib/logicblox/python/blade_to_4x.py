import os, sys
import getopt
import csv

def process_blade(blade_config_dir,converted_config_dir):
    if not os.path.exists(converted_config_dir):
        os.makedirs(converted_config_dir)

    # convert Dimension.csv into 4.x Dimensions.csv
    convert_dimension_file(blade_config_dir, converted_config_dir)

    # # convert Level.csv into 4.x Levels.csv    
    level_dimension_map = {}
    convert_level_file(blade_config_dir, converted_config_dir, level_dimension_map)

    # convert LevelMap.csv and LevelMap_from.csv to 4.x Hierarchies.csv
    convert_hierarchy_file(blade_config_dir, converted_config_dir)

    # convert Intersection.csv to 4.x Intersections.csv
    intersections = convert_intersection_file(blade_config_dir, converted_config_dir, level_dimension_map)

    # convert CompositeAgg.csv to 4.x CompositeAggs.csv
    convert_compositeagg_file(blade_config_dir, converted_config_dir)

    # convert CompositeSpread.csv to 4.x CompositeSpreads.csv
    convert_compositespread_file(blade_config_dir, converted_config_dir)

    # convert Measure.csv to 4.x Measures.csv
    convert_measure_file(blade_config_dir, converted_config_dir, intersections, level_dimension_map)

def load_module_info(blade_config_dir):
    modules = {}

    blade_file = blade_config_dir + "/src/data/Module.csv"
    with open(blade_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            module = ModuleInfo(row["Module"])
            module.intersection = row["baseIntersection"]
            module.datatype = row["dataType"]
            module.defaultvalue = row["defaultValue"]
            module.defaultspread = row["defaultSpread"]
            module.defaultagg = row["defaultAgg"]
            module.format = row["format"]
            module.label = row["label"]
            module.alignment = row["alignment"]
            module.readonly = row["readOnly"]
            module.spreadbymeasure = row["spreadByMeasure"]

            modules[row["Module"]] = module

    return modules

def load_metric_info(blade_config_dir):
    metrics = {}

    blade_file = blade_config_dir + "/src/data/Metric.csv"
    with open(blade_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            metric = MetricInfo(row["Metric"])
            metric.intersection = row["baseIntersection"]
            metric.datatype = row["dataType"]
            metric.defaultspread = row["defaultSpread"]
            metric.defaultagg = row["defaultAgg"]
            metric.format = row["format"]
            metric.label = row["label"]
            metric.alignment = row["alignment"]
            metric.readonly = row["readOnly"]
            metric.spreadbymeasure = row["spreadByMeasure"]

            metrics[row["Metric"]] = metric

    return metrics

def load_version_info(blade_config_dir):
    blade_file = blade_config_dir + "/src/data/Version.csv"

    versions = {}
    with open(blade_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            version = VersionInfo(row["Version"])
            version.intersection = row["baseIntersection"]
            version.datatype = row["dataType"]
            version.defaultspread = row["defaultSpread"]
            version.defaultagg = row["defaultAgg"]
            version.format = row["format"]
            version.label = row["label"]
            version.alignment = row["alignment"]
            version.readonly = row["readOnly"]
            version.spreadbymeasure = row["spreadByMeasure"]

            versions[row["Version"]] = version

    return versions

def load_uom_info(blade_config_dir):
    blade_file = blade_config_dir + "/src/data/Uom.csv"

    UOMs = {}
    with open(blade_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            UOM = UOMInfo(row["Uom"])
            UOM.intersection = row["baseIntersection"]
            UOM.datatype = row["dataType"]
            UOM.defaultspread = row["defaultSpread"]
            UOM.defaultagg = row["defaultAgg"]
            UOM.format = row["format"]
            UOM.label = row["label"]
            UOM.alignment = row["alignment"]
            UOM.readonly = row["readOnly"]
            UOM.spreadbymeasure = row["spreadByMeasure"]

            UOMs[row["Uom"]] = UOM

    return UOMs

def load_role_info(blade_config_dir):
    blade_file = blade_config_dir + "/src/data/Role.csv"

    roles = {}
    with open(blade_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            role = RoleInfo(row["Role"])
            role.intersection = row["baseIntersection"]
            role.datatype = row["dataType"]
            role.defaultspread = row["defaultSpread"]
            role.defaultagg = row["defaultAgg"]
            role.strformat = row["format"]
            role.label = row["label"]
            role.alignment = row["alignment"]
            role.readonly = row["readOnly"]
            role.spreadbymeasure = row["spreadByMeasure"]

            roles[row["Role"]] = role

    return roles

def convert_measure_file(blade_config_dir, converted_config_dir, intersections, level_dimension_map):
    
    # load Module, metric, version, uom, and role info
    metric_infos = load_metric_info(blade_config_dir)
    version_infos = load_version_info(blade_config_dir)
    uom_infos = load_uom_info(blade_config_dir)
    role_infos = load_role_info(blade_config_dir)
    module_infos = load_module_info(blade_config_dir)

    blade_measure_file = blade_config_dir + "/src/data/Measure.csv"
    four_x_measure_filename = converted_config_dir + "/Measures.csv"
    four_x_measure_file = open(four_x_measure_filename, 'w')
    print "Convert " + blade_measure_file + " to " + four_x_measure_filename

    four_x_measure_file.write("Measure,Label,Intersection,DataType,DefaultValue,DefaultAgg,DefaultSpread,RecalcRuleName,PercentBase,PercentParentDimension,Format,HAlignment,Readonly,SpreadByMetric,DerivationType\n")

    with open(blade_measure_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            measure_name = row["Measure"]
            metric = row["metric"]
            version = row["version"]
            uom = row["uom"]
            role = row["role"]
            module = row["module"]

            intersection = find_real_intersection(row["baseIntersectionOverride"], metric_infos.get(metric), 
                                                  version_infos.get(version), 
                                                  uom_infos.get(uom), 
                                                  role_infos.get(role),
                                                  module_infos.get(module), 
                                                  intersections)

            datatype = find_real_datatype(row["dataTypeOverride"], metric_infos.get(metric), 
                                          version_infos.get(version), 
                                          uom_infos.get(uom), 
                                          role_infos.get(role),
                                          module_infos.get(module), 
                                          level_dimension_map)

            defaultvalue = find_real_defaultvalue(row["defaultValueOverride"], datatype, module_infos.get(module))
    
            defaultspread = find_real_defaultspread(row["defaultSpreadOverride"], metric_infos.get(metric), 
                                         version_infos.get(version), 
                                         uom_infos.get(uom), 
                                         role_infos.get(role),
                                         module_infos.get(module))
            defaultagg = find_real_defaultagg(row["defaultAggOverride"], metric_infos.get(metric), 
                                         version_infos.get(version), 
                                         uom_infos.get(uom), 
                                         role_infos.get(role),
                                         module_infos.get(module))

            recalcrule = row["recalcRule"]

            formatstr = find_real_format(row["formatOverride"], metric_infos.get(metric), 
                                         version_infos.get(version), 
                                         uom_infos.get(uom), 
                                         role_infos.get(role),
                                         module_infos.get(module))

            measure_label = find_real_label(row["labelOverride"], metric_infos.get(metric), 
                                          version_infos.get(version), 
                                          uom_infos.get(uom), 
                                          role_infos.get(role),
                                          module_infos.get(module))

            if measure_label == "":
                measure_label = measure_name
            halign = row["alignmentOverride"]
            readonly = row["readOnlyOverride"]
            percentbase = row["percentBase"]
            percentparentdim = row["percentParentDim"]

            spreadbymeasure = find_real_spreadbymeasure(row["spreadByMeasureOverride"],
                                                        metric_infos.get(metric),
                                                        version_infos.get(version), 
                                                        uom_infos.get(uom), 
                                                        role_infos.get(role),
                                                        module_infos.get(module))

            four_x_measure_file.write(",".join([measure_name,measure_label,
                                                intersection,datatype,
                                                defaultvalue,defaultagg,defaultspread,recalcrule,
                                                percentbase,percentparentdim,
                                                formatstr,halign,readonly,spreadbymeasure,""]) + "\n")
        four_x_measure_file.close()

def find_real_spreadbymeasure(spreadbymeasure, metric_info, version_info, uom_info, role_info, module_info):
    new_spreadbymeasure = spreadbymeasure

    if new_spreadbymeasure == "" :
        # try to see whether there's spreadbymeasure specified in the other infos
        if module_info is not None and module_info.spreadbymeasure != "":
            new_spreadbymeasure = module_info.spreadbymeasure
        if role_info is not None and role_info.spreadbymeasure != "":
            new_spreadbymeasure = role_info.spreadbymeasure
        if uom_info is not None and uom_info.spreadbymeasure != "":
            new_spreadbymeasure = uom_info.spreadbymeasure
        if version_info is not None and version_info.spreadbymeasure != "":
            new_spreadbymeasure = version_info.spreadbymeasure
        if metric_info is not None and metric_info.spreadbymeasure != "":
            new_spreadbymeasure = metric_info.spreadbymeasure

    return new_spreadbymeasure

def find_real_label(label, metric_info, version_info, uom_info, role_info, module_info):
    new_label = label
    if new_label == "" :
        names = []
        if metric_info is not None and metric_info.label != "":
            names.append(metric_info.label)
        if version_info is not None and version_info.label != "":
            names.append(version_info.label)
        if uom_info is not None and uom_info.label != "":
            names.append(uom_info.label)
        if role_info is not None and role_info.label != "":
            names.append(role_info.label)
        if module_info is not None and module_info.label != "":
            names.append(module_info.label)

        new_label = " ".join(names)

    return "\"" + new_label + "\""

def find_real_defaultvalue(defval, datatype, module_info):
    new_defval = defval
    if defval == "" :
        if module_info is not None and module_info.defaultvalue != "":
            new_defval = module_info.defaultvalue

    # Blade configurations often do not have default value specified, but they are almost certainly suppose to have default values
    # for numerical measures. We'll set empty default for decimal type measures to 0.0
    #    if defval == "" and datatype == "decimal":
    #        new_defval = "0.0d"
        
    return new_defval

def find_real_defaultspread(defaultspread, metric_info, version_info, uom_info, role_info, module_info):

    new_defaultspread = defaultspread
    if new_defaultspread == "" :
        # try to see whether there's defaultspread specified in the other infos
        if module_info is not None and module_info.defaultspread != "":
            new_defaultspread = module_info.defaultspread
        if role_info is not None and role_info.defaultspread != "":
            new_defaultspread = role_info.defaultspread
        if uom_info is not None and uom_info.defaultspread != "":
            new_defaultspread = uom_info.defaultspread
        if version_info is not None and version_info.defaultspread != "":
            new_defaultspread = version_info.defaultspread
        if metric_info is not None and metric_info.defaultspread != "":
            new_defaultspread = metric_info.defaultspread

    return new_defaultspread

def find_real_defaultagg(defaultagg, metric_info, version_info, uom_info, role_info, module_info):

    new_defaultagg = defaultagg
    if new_defaultagg == "" :
        # try to see whether there's defaultagg specified in the other infos
        if module_info is not None and module_info.defaultagg != "":
            new_defaultagg = module_info.defaultagg
        if role_info is not None and role_info.defaultagg != "":
            new_defaultagg = role_info.defaultagg
        if uom_info is not None and uom_info.defaultagg != "":
            new_defaultagg = uom_info.defaultagg
        if version_info is not None and version_info.defaultagg != "":
            new_defaultagg = version_info.defaultagg
        if metric_info is not None and metric_info.defaultagg != "":
            new_defaultagg = metric_info.defaultagg

    return new_defaultagg

def find_real_format(formatstr, metric_info, version_info, uom_info, role_info, module_info):

    new_format = formatstr
    if new_format == "" :
        # try to see whether there's format specified in the other infos
        if module_info is not None and module_info.format != "":
            new_format = module_info.format
        if role_info is not None and role_info.format != "":
            new_format = role_info.format
        if uom_info is not None and uom_info.format != "":
            new_format = uom_info.format
        if version_info is not None and version_info.format != "":
            new_format = version_info.format
        if metric_info is not None and metric_info.format != "":
            new_format = metric_info.format

    # replace \, with ,
    # add '"' to beginning and end
    new_format = new_format.replace("\,", ",")
    new_format = "\"" + new_format + "\""

    return new_format


def find_real_intersection(intersection, metric_info, version_info, uom_info, 
                           role_info, module_info, intersections):

    new_intersection = intersection
    if new_intersection == "" :
        # try to see whether there's intersection specified in the other infos
        if module_info is not None and module_info.intersection != "":
            new_intersection = module_info.intersection
        if role_info is not None and role_info.intersection != "":
            new_intersection = role_info.intersection
        if uom_info is not None and uom_info.intersection != "":
            new_intersection = uom_info.intersection
        if version_info is not None and version_info.intersection != "":
            new_intersection = version_info.intersection
        if metric_info is not None and metric_info.intersection != "":
            new_intersection = metric_info.intersection

    if new_intersection not in intersections:
        # this means intersection is empty -- scalar
        new_intersection = ""

    return new_intersection

def find_real_datatype(datatype, metric_info, version_info, uom_info, 
                       role_info, module_info, level_to_dim):

    new_datatype = datatype
    if new_datatype == "" :
        # try to see whether there's datatype specified in the other infos
        if module_info is not None and module_info.datatype != "":
            new_datatype = module_info.datatype
        if role_info is not None and role_info.datatype != "":
            new_datatype = role_info.datatype
        if uom_info is not None and uom_info.datatype != "":
            new_datatype = uom_info.datatype
        if version_info is not None and version_info.datatype != "":
            new_datatype = version_info.datatype
        if metric_info is not None and metric_info.datatype != "":
            new_datatype = metric_info.datatype

    new_datatype = make_four_x_type(new_datatype)

    if level_to_dim.has_key(new_datatype):
        dimension = level_to_dim[new_datatype]
        if len(dimension) > 0 :
            new_datatype = dimension + ":" + new_datatype

    return new_datatype

def make_measure_datatype(source_datatype, measure_name, level_to_dim):
    datatype = source_datatype

    # if datatype is not specified, then it is either decimal, or boolean
    # if measure_name starts with Is, then it is a boolean.
    if not datatype:
        if measure_name.startswith("Is"):
            datatype = "boolean"
        else:
            datatype = "decimal"
    
    datatype = make_four_x_type(datatype)

    if level_to_dim.has_key(datatype):
        dimension = level_to_dim[datatype]
        if len(dimension) > 0 :
            datatype = dimension + ":" + datatype

    return datatype

def make_four_x_type(datatype):
    if datatype.startswith("float"):
        return "decimal"
    if datatype.startswith("int") or datatype.startswith("uint"):
        return "int"
    if datatype.startswith("decimal"):
        return "decimal"
    if datatype == "color":
        return "string"
    return datatype

def convert_compositeagg_file(blade_config_dir, converted_config_dir):
    # CompositeAgg.csv headers
    # name,order,aggMethod,kind,role
    #
    # Convert to:
    # Name,Order,AggMethod,Key
    blade_compositeagg_file = blade_config_dir + "/src/data/CompositeAgg.csv"
    four_x_compositeagg_filename = converted_config_dir + "/CompositeAggs.csv"
    four_x_compositeagg_file = open(four_x_compositeagg_filename, 'w')
    print "Convert " + blade_compositeagg_file + " to " + four_x_compositeagg_filename

    four_x_compositeagg_file.write("Name,Order,AggMethod,Key\n")
    
    with open(blade_compositeagg_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            agg_name = row["name"]
            order = row["order"]
            agg_method = row["aggMethod"]
            key_dimension = row["kind"]

            four_x_compositeagg_file.write(",".join([agg_name, order, agg_method, key_dimension]) + "\n")

    four_x_compositeagg_file.close()

def convert_compositespread_file(blade_config_dir, converted_config_dir):
    # CompositeSpread.csv headers
    # name,order,spreadMethod,kind,role
    #
    # Convert to:
    # Name,Order,SpreadMethod,Key
    blade_compositespread_file = blade_config_dir + "/src/data/CompositeSpread.csv"
    four_x_compositespread_filename = converted_config_dir + "/CompositeSpreads.csv"
    four_x_compositespread_file = open(four_x_compositespread_filename, 'w')
    print "Convert " + blade_compositespread_file + " to " + four_x_compositespread_filename

    four_x_compositespread_file.write("Name,Order,SpreadMethod,Key\n")
    
    with open(blade_compositespread_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            agg_name = row["name"]
            order = row["order"]
            spread_method = row["spreadMethod"]
            key_dimension = row["kind"]

            four_x_compositespread_file.write(",".join([agg_name, order, spread_method, key_dimension]) + "\n")

    four_x_compositespread_file.close()
    
def convert_intersection_file(blade_config_dir, converted_config_dir, level_dimension_map):
    # Intersection.csv headers
    # Intersection,Order8,levels
    #
    # Convert to
    # Intersection,Order,Dimension,Level
    blade_intersection_file = blade_config_dir + "/src/data/Intersection.csv"
    four_x_intersection_filename = converted_config_dir + "/Intersections.csv"
    four_x_intersection_file = open(four_x_intersection_filename, 'w')
    print "Convert " + blade_intersection_file + " to " + four_x_intersection_filename

    four_x_intersection_file.write("Intersection,Order,Dimension,Level\n")

    intersections = []

    with open(blade_intersection_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            intersection = row["Intersection"]
            order = row["Order8"]
            level = row["levels"]

            if not level == "" :
                four_x_intersection_file.write(",".join([intersection, order, level_dimension_map.get(level), level]) 
                                               + "\n")
                intersections.append(intersection)

    four_x_intersection_file.close()
    return set(intersections)

def convert_dimension_file(blade_config_dir, converted_config_dir):
    # Dimension.csv headers
    # Dimension,label,nameSpace,primaryRoot,securityLevel,workBookPartitionLevel
    # 
    # Convert to:
    # Dimension,Label
    blade_dimension_file = blade_config_dir + "/src/data/Dimension.csv"
    filename = converted_config_dir + "/Dimensions.csv"
    four_x_dim_file = open(filename, 'w')
    
    print "Convert " + blade_dimension_file + " to " + filename

    four_x_dim_file.write("Dimension,Label\n")
    
    with open(blade_dimension_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            dimension = row["Dimension"]
            label = row["label"]

            four_x_dim_file.write(",".join([dimension, label]) + "\n")

    four_x_dim_file.close()

def convert_level_file(blade_config_dir, converted_config_dir, level_dimension_map):
    # Level.csv headers
    # Level,capacity,dimension,elementType,isOrdered,label,isUnfiltered    
    #
    # Convert to:
    # Level,Label,Dimension,ElementType,IsOrdered,OrderAttribute
    blade_level_file = blade_config_dir + "/src/data/Level.csv"
    filename = converted_config_dir + "/Levels.csv"
    four_x_level_file = open(filename, 'w')

    print "Convert " + blade_level_file + " to " + filename

    four_x_level_file.write("Level,Label,Dimension,ElementType,IsOrdered,OrderAttribute\n")

    with open(blade_level_file, 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            level = row["Level"]
            dimension = row["dimension"]
            element_type = get_four_x_type(row["elementType"])
            is_ordered = row["isOrdered"]
            label = row["label"]

            level_dimension_map[level] = dimension

            four_x_level_file.write(",".join([level,label,dimension,element_type,is_ordered,""])+ "\n")
    
    four_x_level_file.close()

def convert_hierarchy_file(blade_config_dir, converted_config_dir):
    # LevelMap.csv headers
    # LevelMap,label,dimension,isPrimary,toLevel
    # 
    # LevelMap_from.csv headers
    # LevelMap,Order8,fromLevels
    #
    # Convert to:
    # Hierarchy,Dimension,IsDefault,FromLevel,ToLevel,Index,HasFirst,HasLast

    # paths_by_dimension has the following structure
    # dimension : [ (from, to), ... ] 
    paths_by_dimension = populate_paths_by_dimension(blade_config_dir)

    # find hierarchies per dimension
    # { dimension : [ hier1, hier2, ... ] }
    complete_hierarchies_by_dimension = complete_hierarchies(paths_by_dimension)

    filename = converted_config_dir + "/Hierarchies.csv"
    four_x_hierarchy_file = open(filename, 'w')
    
    print "Convert " + filename
    
    four_x_hierarchy_file.write("Hierarchy,Dimension,IsDefault,FromLevel,ToLevel,Index,HasFirst,HasLast\n")

    for dimension in complete_hierarchies_by_dimension.keys() :
        hier_index = 0
                
        for hierarchy in complete_hierarchies_by_dimension.get(dimension) :
            # name the hierarchy -- dimension + index.
            hierarchy_name = dimension + "_" + str(hier_index)
            
            path_index = 0
            for path in hierarchy.get_paths():
                four_x_hierarchy_file.write(",".join([hierarchy_name,dimension,str(hierarchy.is_primary).lower(),
                                                      path[0],path[1],
                                                      str(path_index),
                                                      # TODO: need to set HasFirst and HasLast appropriately from IsOrdered
                                                      "",""]) + "\n")
                path_index += 1

            hier_index += 1

    four_x_hierarchy_file.close()

def complete_hierarchies(paths_by_dimension) :
    complete_hierarchies_by_dimension = {}

    for dimension in paths_by_dimension.keys():
        paths = paths_by_dimension.get(dimension)

        start_hierarchies = find_start_hierarchies(paths)
        paths_by_from_levels = populate_paths_by_from_levels(paths)

        # list of completed hierarchies.
        complete_hierarchies = [] 
        # list of hierarchies that still need work
        hierarchy_worklist = []

        # for each start_hierarchy
        # search for paths that can extend its top-level
        # if found, extend the hierarchy and append new hierarchy to the worklist
        # otherwise, add hierarchy to complete_hierarchys
        # work until start_hierarchies is empty.
        while len(start_hierarchies) > 0 :
            for hierarchy in start_hierarchies :
                top_level = hierarchy.get_top_level()

                # find all paths that start with top_level
                if paths_by_from_levels.has_key(top_level) :
                    new_paths = paths_by_from_levels.get(top_level)

                    # extend this hierarchy with new paths.
                    for new_path in new_paths :
                        new_hier = hierarchy.copy()
                        new_hier.add_path(new_path)

                        # add new_hier to the worklist
                        hierarchy_worklist.append(new_hier)
                else:
                    # this hierarchy is done.
                    complete_hierarchies.append(hierarchy)
            
            start_hierarchies = hierarchy_worklist
            hierarchy_worklist = []
            
        # if we're here, we've found all hierarchies by this dimension.
        complete_hierarchies_by_dimension[dimension] = complete_hierarchies

    return complete_hierarchies_by_dimension

def populate_paths_by_dimension(blade_config_dir):
    # levelmap_from { levelmapname : from_level }
    levelmap_from = {}
    # levelmap_to { levelmapname : to_level }
    levelmap_to = {}
    # levelmap_dimension { levelmapname : dimension }
    levelmap_dimension = {}
    # 
    levelmap_isprimary = {}

    with open(blade_config_dir + "/src/data/LevelMap.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            levelmap_to[row["LevelMap"]] = row["toLevel"]
            levelmap_dimension[row["LevelMap"]] = row["dimension"]
            levelmap_isprimary[row["LevelMap"]] = row["isPrimary"]
            
    with open(blade_config_dir + "/src/data/LevelMap_fromLevels.csv", 'rb') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["Order8"] == '0':
                levelmap_from[row["LevelMap"]] = row["fromLevels"]

    # paths_by_dimension has the following structure
    # dimension : [ (from, to, isprimary), ... ] 
    paths_by_dimension = {}

    for levelmap in levelmap_from.keys():
        from_level = levelmap_from[levelmap]
        to_level = levelmap_to[levelmap]
        dimension = levelmap_dimension[levelmap]
        is_primary = levelmap_isprimary[levelmap]
            
        if dimension in paths_by_dimension.keys():
            paths = paths_by_dimension.get(dimension)
            paths.append( (from_level, to_level, is_primary) )
        else:
            paths = []
            paths.append( (from_level, to_level, is_primary) )
            paths_by_dimension[dimension] = paths

    return paths_by_dimension

# find a list of paths (from, to) where
# each "from" has no other paths that use it as a "to"
# construct initial set of hierarchies.
def find_start_hierarchies(paths):
    # to_levels: all levels that appear in a to position
    to_levels = []
    for path in paths :
        to_levels.append(path[1])

    # find root paths -- paths from which hierarchies must start
    # these are pairs (from, to) where from does not appear in any other pair as to
    to_levels_set = set(to_levels)
    start_hierarchies = []
    for path in paths :
        from_level = path[0]
        if from_level not in to_levels_set:
            hierarchy = Hierarchy()
            hierarchy.add_path(path)
            start_hierarchies.append(hierarchy)

    return start_hierarchies

class VersionInfo:
    def __init__(self, name):
        self.name = name
        self.intersection = ""
        self.datatype = ""
        self.defaultspread = ""
        self.defaultagg = ""
        self.format =  ""
        self.label = ""
        self.alignment = ""
        self.readonly = ""
        self.spreadbymeasure = ""        

class UOMInfo:
    def __init__(self, name):
        self.name = name
        self.intersection = ""
        self.datatype = ""
        self.defaultspread = ""
        self.defaultagg = ""
        self.format =  ""
        self.label = ""
        self.alignment = ""
        self.readonly = ""
        self.spreadbymeasure = ""        

class RoleInfo:
    def __init__(self, name):
        self.name = name
        self.intersection = ""
        self.datatype = ""
        self.defaultspread = ""
        self.defaultagg = ""
        self.format =  ""
        self.label = ""
        self.alignment = ""
        self.readonly = ""
        self.spreadbymeasure = ""        

class MetricInfo:
    def __init__(self, name):
        self.name = name
        self.intersection = ""
        self.datatype = ""
        self.defaultspread = ""
        self.defaultagg = ""
        self.format =  ""
        self.label = ""
        self.alignment = ""
        self.readonly = ""
        self.spreadbymeasure = ""

class ModuleInfo:
    def __init__(self, name):
        self.name = name
        self.intersection = ""
        self.datatype = ""
        self.defaultvalue = ""
        self.defaultspread = ""
        self.defaultagg = ""
        self.format =  ""
        self.label = ""
        self.alignment = ""
        self.readonly = ""
        self.spreadbymeasure = ""
    
class Hierarchy :
    def __init__(self):
        # path is a list of (from, to, is_primary)
        self.paths = []
        self.is_primary = True

    def add_path(self, path):
        self.paths.append(path)
        if len(path[2]) == 0 :
            self.is_primary = False
    
    def get_top_level(self):
        if len(self.paths) == 0:
            return None
        last_path = self.paths[len(self.paths)-1]
        return last_path[1]

    def copy(self):
        new_hier = Hierarchy()
        new_hier.paths = list(self.paths)
        new_hier.is_primary = self.is_primary
        return new_hier

    def get_paths(self):
        return self.paths

# return a dictionary of
# { from_level: [ path1, ... ] }
# where each path_n start with from_level
def populate_paths_by_from_levels(paths):
    path_by_from_levels = {}
    for path in paths :
        from_level = path[0]

        if from_level in path_by_from_levels.keys():
            paths = path_by_from_levels.get(from_level)
            paths.append(path)
        else:
            path_by_from_levels[from_level] = [ path ]

    return path_by_from_levels

def get_four_x_type(element_type):
    if element_type.startswith("float"):
        return "float"
    elif element_type.startswith("decimal"):
        return "decimal"
    elif element_type.startswith("int"):
        return "int"
    elif element_type.startswith("uint"):
        return "int"
    elif element_type.startswith("decimal"):
        return "decimal"
    return element_type

def main(argv=None):
    if argv is None:
        argv = sys.argv
    try:
        opts, args = getopt.getopt(argv[1:], "h", ["help"])
    except getopt.error, msg:
        print msg
        print "for help use --help"
        sys.exit(2)
    for o, a in opts:
        if o in ("-h", "--help"):
            print "TODO help"
            sys.exit(0)

    blade_config_dir = args[0]
    converted_config_dir = args[1]
    process_blade(blade_config_dir, converted_config_dir)

if __name__ == '__main__': main()
