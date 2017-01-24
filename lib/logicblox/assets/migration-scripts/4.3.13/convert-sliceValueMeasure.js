"use strict";

var fs = require("fs");
var path = require("path");

var folder = process.argv[2];

console.log("Sheets folder is", folder);
console.log();

var configs = readConfigs(folder, /\.json$/),
    updatedConfigs = {};

console.log();

// Removing sliceValueMeasure
// from pivotConfig and creating signals and listeners
Object.keys(configs).forEach(function(fullPath) {
    var config = configs[fullPath];

    if (config.pivotConfig && config.pivotConfig.sliceValueMeasure) {
        config.signals = config.signals || {};
        config.signals.output = config.signals.output || [];
        config.signals.input = config.signals.input || [];

        var output = config.pivotConfig.sliceValueMeasure.map(function(item) {
            console.log("Create signal", item.measure, "for", fullPath);

            return {
                dataType: "POSITIONS",
                emitterId: createComponentId(item),
                eventName: "Slice Change",
                name: createSignalName(item),
                init: {
                    value: [{
                        measure: item.measure,
                        qualifiedName: item.qualifiedName
                    }]
                }
            };
        });

        var input = config.pivotConfig.sliceValueMeasure.map(function(item) {
            console.log("Create listener", item.measure, "for", fullPath);

            return {
                handler: "changeSliceSignalHandler",
                listenerId: createComponentId(item),
                signalName: createSignalName(item)
            };
        });

        config.signals.output = config.signals.output.concat(output);
        config.signals.input = config.signals.input.concat(input);

        config.pivotConfig.sliceValueMeasure = undefined;
        updatedConfigs[fullPath] = config;
    }
});

console.log();

writeConfigs(updatedConfigs);

function readConfigs(folder, regexp) {
    var filenames = fs.readdirSync(folder);

    return filenames
        .filter(function(filename) {
            return regexp.test(filename);
        })
        .reduce(function(memo, filename) {
            console.log("Read", filename);

            var fullPath = path.join(folder, filename),
                textConfig = fs.readFileSync(fullPath, {
                    encoding: "utf-8"
                });

            memo[fullPath] = JSON.parse(textConfig);

            return memo;
        }, {});
}

function writeConfigs(configs) {
    Object.keys(configs).forEach(function(fullPath) {
        var config = configs[fullPath];

        console.log("Write", fullPath);
        fs.writeFileSync(fullPath, JSON.stringify(config, undefined, 4), {
            encoding: "utf-8"
        });
    });
}

function createSignalName(item) {
    return "Slice@" + item.qualifiedName + "@" + item.measure;
}

function createComponentId(item) {
    return "Slice@" + item.qualifiedName;
}