/* eslint-env node */

"use strict";

var fs = require('fs');
var path = require('path');
var parseArgs = require('minimist');
var logicbloxtestutils = require("logicbloxtestutils");
var ModelerTestUtil = logicbloxtestutils.ModelerTestUtil;

/**
 * Script to warmup views in an application.
 * Assumes canvases sheets are in src/config/canvas. Another one can be passed
 * in using the --config-dir parameter.
 * 
 * Mandatory paramters are --app-prefix
 *
 * Optional parameters:
 * - server-url (default http://localhost:55183)
 * - config-dir (default src/config/canvas)
 * - canvas (id of a canvas if we want to warmup just one canvas)
 */

if (require.main === module) {

    var argv = parseArgs(process.argv.slice(2), {
            default: {
                "config-dir": "./src/config/canvas",
                "server-url": "http://localhost:55183",
            },
        }),
        serverUrl = argv["server-url"],
        canvasesPath = argv["config-dir"],
        appPrefix = argv["app-prefix"],
        saveQueriesTo = argv._[0],
        modelerTestUtil = new ModelerTestUtil({
            appPrefix: serverUrl + "/" + appPrefix,
            workspace: "foo" // modelerTestUilt requires workspace but we don't need it for warmups
        }),
        modelerInitialized = initializeModeler(modelerTestUtil),
        canvasIdsPromise = findCanvasIds(canvasesPath);

    Promise.all([modelerInitialized, canvasIdsPromise]).then(function(result) {
        var canvasIds = result[1]; 

        console.log("Saving warmup queries for canvases to " + saveQueriesTo);
        return generateWarmupQueries(removeEmpty(canvasIds))
            .then(function(warmupQuery) {
                return saveQuery(saveQueriesTo, warmupQuery);
            });
    }).then(process.exit).catch(function(err) {
        console.error(err.stack);
        process.exit();
    });

}

function removeEmpty(qs) { 
    return qs.filter(function(q) { return q; }); 
}

function findCanvases(canvasesPath) {
    return listFilesIn(canvasesPath).then(function(fileNames) {
        return fileNames.filter(function(filePath) {
            var isJson = filePath.endsWith('.json'),
                isTemplate = filePath.indexOf('/templates/') !== -1;

            return isJson && !isTemplate;
        });        
    }).catch(function(err) {
        console.error(err.stack);
        process.exit();
    });
}

function initializeModeler(modelerTestUtil) {
    return modelerTestUtil.modelerApp
        .getModelerActionHandler().initializeModeler()
        .catch(function(err) {
            console.error(err.stack);
            process.exit();
        });
}

function generateWarmupQueries(canvasIds) {
    return modelerTestUtil.generateWarmupQueries(canvasIds).then(function(r) {
        return {
            canvasIds: canvasIds,
            query: r
        };
    }).catch(function(err) {
        console.error("Error generating queries for " + canvasIds +
            ". Look into server log for more details");
        console.error(err.stack);
    });
}


/**
 * Builds a promise for reading files
 *
 * @param  {String[]}  canvasFiles array of canvas files paths
 * @return {Promise[]} 
 */
function readFile(filePath) {
    return new Promise(function(resolve,reject){
        fs.readFile(filePath, function(err, data) {
            if (err) reject(err);
            else resolve({
                filename: filePath,
                data: JSON.parse(data)
            });
        });
    });
}


function findCanvasIds(canvasesPath) {
    return findCanvases(canvasesPath).then(function(canvasFiles) {
        return Promise.all(canvasFiles.map(readFile)).then(function(canvases) {
            return canvases.map(function(canvasFile){
                var canvas = canvasFile.data;

                if (!canvas.id) {
                    console.warn("Could not find id for " + canvasFile.filename);
                }
                return canvas.id;
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

function saveQuery(saveQueriesTo, warmupQuery) {
    var exprs = warmupQuery.query.install_request.measure_expr,
        query = {};

    // we generate an empty request if we don't have any query expressions
    // to avoid getting 500 errors from measure service since measure expressions
    // are mandatory for install_requests
    if (exprs.length > 0) {
        query = {
            install_request: {
                measure_expr: exprs
            }
        };        
    }

    var filename = saveQueriesTo + "/view-queries.json";
    return saveRequest(filename, query);
}

function saveRequest(filename, warmupQuery) {
    fs.writeFileSync(filename, JSON.stringify(warmupQuery));
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
