#!/bin/bash

TOPOS=("diamond" "diamondext" "fattree")

for topo in ${TOPOS[*]}
do
    cmd=`./netgen.py --topo=$topo --spec=specs/$topo.txt`
    found=`echo "$cmd" | grep -A 3 -i "model" | grep -v "*"`
    if [ found ]; then
	echo -e "[PASSED]" $topo "\t" $found
    else
	echo -e "[FAILED]" $topo "\t" $found
    fi
done
