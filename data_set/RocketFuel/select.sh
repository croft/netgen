#!/usr/bin/bash
filename="select.txt"
while read -r line
do
    name=$line
    cp class/$name selected/$name
done < "$filename"