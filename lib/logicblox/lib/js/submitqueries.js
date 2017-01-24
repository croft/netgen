/* eslint-env node */

"use strict";

var fs = require('fs');
var path = require('path');
var parseArgs = require('minimist');
var logicbloxtestutils = require("logicbloxtestutils");
var HttpHelper = logicbloxtestutils.HttpHelper;

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
                "server-url": "http://localhost:55183"
            },
        }),
        serverUrl = argv["server-url"],
        appPrefix = argv["app-prefix"],
        failOnError = argv["fail-on-error"],
        queryDir = argv._[0],
        measureUrl = serverUrl + "/" + appPrefix + "/measure",
        http = new HttpHelper();

    listFilesIn(queryDir).then(function(filenames) {
        return executeSequentially(filenames.map(buildWarmupFunction.bind(null, measureUrl)), failOnError);
    }).then(process.exit).catch(function(err) {
        console.error(err.stack || err);
        process.exit(1);
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
            else resolve(JSON.parse(data));
        });
    });
}

function warmupSheet(query, measureUrl) {
    return http.post(measureUrl, query);
}

/**
 * Returns a promise factory for quering out a view
 *
 * @param  {Object}  data view data ( from canvas file )
 * @return {Function} 
 */
function buildWarmupFunction(measureUrl, filename) {
    return function() {
        console.log("Submitting " + filename);
        return readFile(filename).then(function(query) {
            var start = Date.now() / 1000;
            return warmupSheet(query, measureUrl).then(function() {
                var end = Date.now() / 1000;
                // this is used for benchmarks reporint, don't change the format!
                console.log("#REPORT# warmup-" + [filename, start, end, end-start].join(","));
            });
        });
    };
}


function listFilesIn(dir) {
    return new Promise(function(resolve, reject) {
        walk(dir, function(err, result) {
            if (err) reject(err);
            else resolve(result);
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


/**
 * A function to execute promises sequentially
 *
 * @param  {Array}  promiseFactories array of promises
 * @param  {boolean} failOnError     if one of the promises fail, this will throw and exception.
 *                                   Otherwise, it will just log the error and continue execution.
 * @return {Promise} 
 */
function executeSequentially(promiseFactories, failOnError) {
    var result = Promise.resolve(),
        error;
    promiseFactories.forEach(function (fn) {
        result = result.then(function(){
            if (!failOnError || !error) {
                return fn();
            }
        }).catch(function (err) {
            if (!failOnError) {
                console.warn(err.stack);               
            } else {
                error = err;
            }
        });            
    });
    return result.then(function () {
        if (error && failOnError) {
            throw error;
        }    
    });
}
