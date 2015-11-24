#!/bin/bash
FILES=svg/*
for f in $FILES
do
  name=$(basename $f)

  dot -Tsvg -o pic/$name.svg svg/$name

done