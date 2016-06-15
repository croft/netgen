#!/bin/bash

set -e
set -o nounset

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
RESULTDIR=results
TESTFILE=encodings.py

THEORIES=("LIA" "BV")
ENCODINGS=("UF" "MACRO")
TOPOS=("fattree" "rocketfuel" "stanford")

OUTPUT=tmp.encodings.out

mkdir -p $DIR/$RESULTDIR
rm -rf $OUTPUT

for theory in ${THEORIES[*]}
do
    for encoding in ${ENCODINGS[*]}
    do
	for topo in ${TOPOS[*]}
	do
	    echo "Testing $theory $encoding $topo"
	    cd $DIR
	    cd ../solver/
	    cp configs/config_${theory}_${encoding}.h config.h
	    make clean > /dev/null
	    make all > /dev/null

	    cd $DIR
	    python $TESTFILE $topo $theory $encoding $RESULTDIR >> $OUTPUT 2>&1
	done
    done
done
