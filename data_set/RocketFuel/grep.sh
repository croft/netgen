for f in *
do
  grep  "10.0.3.102"  $f #| xargs grep -l "10.0.1.153" | xargs grep -l "10.0.2.154"

done