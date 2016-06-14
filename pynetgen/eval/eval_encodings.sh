#!/bin/bash

set -e
set -o nounset

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
RESULTS=results
TESTFILE=encodings.py

THEORIES=("LIA" "BV")
ENCODINGS=("UF" "MACRO")
TOPOS=("fattree" "rocketfuel" "stanford")


mkdir -p $DIR/$RESULTDIR

for theory in ${THEORIES[*]}
do
    for encoding in ${ENCODINGS[*]}
    do
	for topo in ${TOPOS[*]}
	do
	    echo "Testing $theory $encoding"
	    cd $DIR
	    cd ../solver/
	    cp configs/config_${theory}_${encoding}.h config.h
	    make clean > /dev/null
	    make all > /dev/null

	    cd $DIR
	    python $TESTFILE $topo $theory $encoding $results
	done
    done
done
