/* globals console */
"use strict";

var fs = require("fs");
var path = require("path");

/**
 * Usage: node migrate-sheets.js [SHEET-FOLDER]
 */

var argv = process.argv.slice(2);

function readSheet(filename) {
    var s = fs.readFileSync(filename);
    try {
        return JSON.parse(s);    
    } catch(err) {
        console.error(err);
        console.error("Error converting " + filename + " to JSON.");
    }
    
}

function saveSheet(filename, sheet) {
    fs.writeFileSync(filename, JSON.stringify(sheet, null, 4));
}

function findSheets(folder) {
    return listFilesIn(folder).then(function(filenames) {
        return filenames.map(function(filename) {
            var sheet = readSheet(filename);    
            return {filename: filename, sheet: sheet};            
        }).filter(function(s) {
            return s.sheet;
        });
    });
}

/**
 * Synchronous function for recursively listing files in a directory 
 *
 * @param  {String}   dir   path of the directory to read from
 * @param  {Function} done  callback to execute when finished
 */
function walk(dir, done) {
    var results = [];
    fs.readdir(dir, function(err, list) {
        if (err) return done(err);
        var pending = list.length;
        if (!pending) return done(null, results);
        list.forEach(function(file) {
            file = path.resolve(dir, file);
            fs.stat(file, function(err, stat) {
                if (stat && stat.isDirectory()) {
                    walk(file, function(err, res) {
                        results = results.concat(res);
                        if (!--pending) done(null, results);
                    });
                } else {
                    results.push(file);
                    if (!--pending) done(null, results);
                }
            });
        });
    });
}

function listFilesIn(dir) {
    return new Promise(function(resolve, reject) {
        walk(dir, function(err, result) {
            if (err) reject(err);
            else resolve(result);
        });
    });
}

function forEachInObj(obj, fn) {
    Object.keys(obj).forEach(function (key) {
        var v = obj[key];
        fn(v, key);
    });
}

function find(l, fn) {
    var result;
    l.forEach(function(item) {
        if (fn(item)) {
            result = item;
        }
    });
    return result;
}

function findIndex(l, fn) {
    var result;
    l.forEach(function(item, i) {
        if (fn(item)) {
            result = i;
        }
    });
    return result;
}


function convertOldPivotConfigToNew(oldPivotConfig, viewId) {
    //if there's no aggregate defined, just return the prior config as we don't do anything else currently
    if (!oldPivotConfig.aggregate) return oldPivotConfig;
    var newPivotConfig = oldPivotConfig;


    //basically if there is an aggregate defined,
    //then loop through the axes and
    //  if the qName of an aggregate appears and it doesn't have a rollup property configured on it,
    //  update it to have it.  If it does have a rollup property, warn that we're ignoring the aggregate definition
    //
    //  if the qName of an aggregate does not appear but a qName of the same dimension Does appear, add
    //  a field for this qName next to the first one we find (we'll reorder them later) and set the rollup
    //  property for that field and set its displayMode to NONE
    forEachInObj(newPivotConfig.aggregate, function(aggDef, key) {
        var qName = aggDef.qualifiedName || key,
            isMeasure = isMeasureFn(qName),
            isLevel = !isMeasure,
            ql = isLevel && parseDimLvl(qName),
            aggDim = ql && ql.dimension,
            aggLabel = ql && ql.label,
            matchingField,
            matchingFieldAxisName,
            aggAxisName,
            insertIdx;
                
        // Search all axes for a matching field. If a matching field is found, stop search. Otherwise,
        // keep track of any field that is on the same dimension as agg field and continue the search.
        forEachInObj(newPivotConfig.axis, function(pivotFields, axisName) {
            var matchingFieldInAxis = find(pivotFields, function(f) {
                    return f.qualifiedName === qName;
                }),
                sameDimIdx = isLevel && !matchingFieldInAxis && findIndex(pivotFields, function(f) {
                    return !isMeasureFn(f.qualifiedName) && parseDimLvl(f.qualifiedName).dimension === aggDim;
                });

            if (matchingFieldInAxis) {
                matchingField = matchingFieldInAxis;
                matchingFieldAxisName = axisName;
            } else if (isLevel && sameDimIdx > -1) {
                aggAxisName = axisName;
                insertIdx = sameDimIdx;
            }
        });

        if (matchingField) {
            if (matchingFieldAxisName === "slice" && isLevel && insertIdx > -1) {
                // If the matching field is on the slice and if there is another level from the same dim in on an axis, add "ALL" level to the axis.
                newPivotConfig.axis[aggAxisName].splice(insertIdx, 0, createLevelFieldConfig(qualifiedName(aggDim, "ALL", aggLabel), undefined, undefined, { methodName: aggDef.method || "DEFAULT" }));
            } else if (matchingField.rollup)
                console.warn("discarding aggregate definition for '" + qName + "' in pivot '" + viewId + "' because the associated field already has a rollup defined."); 
            else
                matchingField.rollup = { methodName: aggDef.method || "DEFAULT" };
        } else if (isLevel && insertIdx > -1) {
            newPivotConfig.axis[aggAxisName].splice(insertIdx, 0, createLevelFieldConfig(qName, undefined, "NONE", { methodName: aggDef.method || "DEFAULT" }));
        } else {
            throw Error("Could not convert agg aggDef " + JSON.stringify(aggDef) + 
                ". Could not find axis with dimension " + aggDim + "' in sheet '" + viewId + "'" + ". Please either fix the aggregation config.");
        }
    });
    delete newPivotConfig.aggregate;

    return newPivotConfig;
}

function createLevelFieldConfig(qName, value, displayMode, rollup) {
    var config = { 
        qualifiedName: qName,
        displayMode: displayMode || "OUTLINE"
    };
    if (rollup) {
        config.rollup = rollup;
    }

    if (value) {
        config.value = value;
    }
    
    return config;
}

function isMeasureFn(key) {
    return (key.indexOf(":") === -1);
}

function parseDimLvl(s, includeLabel) {
    includeLabel = !!includeLabel;
    var ss = s.split(":");
    if (!includeLabel) {
        return {dimension: ss[0], level: ss[1]};
    } else {
        if (ss.length === 2)
            return {dimension: ss[0], level: ss[1]};
        else 
            return {label: ss[0], dimension: ss[1], level: ss[2]};
    }
}

function qualifiedName(dimension, level, label) {
    return ((undefined === label) ? dimension : label) + ":" + ((undefined === level) ? "" : level);
}

if (require.main === module) {
    var folder = argv[0],
        sheets = findSheets(folder);

    sheets.then(function(sheets) {
        sheets.forEach(function(s) {
            var sheet = s.sheet,
                filename = s.filename;

            if (!sheet.pivotConfig) {
                console.error("File " + filename + " is probably not a sheet since it doesn't have a pivotConfig");
            }
            else {
                console.log("Converting sheet " + filename);
                try {
                    sheet.pivotConfig = convertOldPivotConfigToNew(sheet.pivotConfig, sheet.id);
                } catch (err) {
                    console.error("Error converting sheet " + filename);
                    throw err;
                }
                saveSheet(filename, sheet);                    
            }
        });
    }).catch(function(err) {
        console.error(err.stack);
    });
}
