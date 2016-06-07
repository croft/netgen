#!/bin/bash

set -e
set -o nounset

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
RESULTDIR=results
THEORIES=("LIA" "BV" "LRA")
ENCODINGS=("UF" "MACRO")

mkdir -p $DIR/$RESULTDIR

for theory in ${THEORIES[*]}
do
    for encoding in ${ENCODINGS[*]}
    do
	cd $DIR
	cd ../solver/
	cp configs/config_${theory}_${encoding}.h config.h
	make

	cd $DIR
	destfile=$RESULTDIR/result_${theory}_${encoding}.txt
	rm -f $destfile

	./perf.py -c >> $destfile
    done
done
