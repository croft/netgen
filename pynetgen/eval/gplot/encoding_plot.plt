reset
set termoption dash

set style line 80 lt -1 lc rgb "#808080"
set style line 81 lt 0  # dashed
set style line 81 lt rgb "#808080"
#set grid back linestyle 81
set grid ytics linestyle 81
set border 3 back linestyle 80

set style data histogram
#set style histogram cluster gap 1
set style histogram errorbars gap 1 lw 1
set style fill solid border -1
set boxwidth 0.9

set output 'encoding_plot.pdf'
set terminal pdfcairo size 4, 2 font "Gill Sans, 8" linewidth 2 rounded fontscale 1

set multiplot
unset xtics
set ytics font ',6' offset 0.5
set xtics font ',6'

unset key

# ovs plot
set tmargin at screen 0.80
set bmargin at screen 0.25
set lmargin at screen 0.13
set rmargin at screen 0.95
set auto x
set yrange[0:10]
unset xlabel
#unset xtics
set ylabel "Synthesis Time (ms)" offset 2.2,0
set xlabel "Network" font "Gill Sans, 8" offset 0,0.3
#set label "ovs-ofctl" font "Gill Sans, 8" at graph 0.18,1.125
plot 'encodings.dat' using 2:3:4:xtic(1) title col lc rgb "#920000", \
     '' using 5:6:7 title col lc rgb "#006ddb", \
     '' using 8:9:10 title col lc rgb "#dbd100", \
     '' using 11:12:13 title col lc rgb "#a6a6a6"


unset ylabel
unset xlabel
unset label

# key
#set tmargin at screen 0.1
set bmargin at screen 1.0
# set lmargin at screen 0.0
# set rmargin at screen 1

unset label
unset ytics
unset tics
unset xlabel
unset ylabel
set border 0

set key horiz
set key samplen 1 spacing 0.75 font "Gill Sans,8" maxcols 2
set yrange [0:1]
set style data histograms

plot NaN t "LIA + UF" w boxes lc rgb "#920000", \
     NaN t "LIA + MACRO" w boxes lc rgb "#006ddb", \
     NaN t "BV + UF" w boxes lc rgb "#dbd100", \
     NaN t "BV + MACRO" w boxes lc rgb "#a6a6a6"

