#!/bin/sh
for i in $( ls *.lhs); do
    lhs2TeX --poly $i | sed '1,92d' > ${i%.lhs}.tex
done

##lhs2TeX --poly Introduction.lhs > I


