#!/bin/bash

set -e
set -o nounset

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
RESULTDIR=results
TESTFILE=macrotime.py

THEORY="LIA"
ENCODING="MACRO"
TOPOS=("fattree" "rocketfuel" "stanford")

OUTPUT=tmp.macrotime.out

mkdir -p $DIR/$RESULTDIR
rm -rf $OUTPUT

for topo in ${TOPOS[*]}
do
    echo "Testing $THEORY $ENCODING $topo"
    cd $DIR
    cd ../solver/
    cp configs/config_${THEORY}_${ENCODING}.h config.h
    make clean > /dev/null
    make all > /dev/null

    cd $DIR
    python $TESTFILE $topo $RESULTDIR >> $OUTPUT 2>&1
done
