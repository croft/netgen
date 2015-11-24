#!/bin/bash
filename="classes"
while read -r line
do
    name=$line
    cp ../RocketFuel/class/$name selected/$name
    echo "$name"
done < "$filename"