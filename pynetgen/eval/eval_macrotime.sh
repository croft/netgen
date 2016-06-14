#!/bin/bash

set -e
set -o nounset

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
RESULTS=results
TESTFILE=macrotime.py

THEORIES="LIA"
ENCODINGS="UF"
TOPOS=("fattree" "rocketfuel" "stanford")

mkdir -p $DIR/$RESULTDIR

for theory in ${THEORIES[*]}
do
    echo "Testing $THEORY $ENCODING"
    cd $DIR
    cd ../solver/
    cp configs/config_${THEORY}_${ENCODING}.h config.h
    make clean > /dev/null
    make all > /dev/null

    cd $DIR
    python $TESTFILE $topo $results
done
