<./latex.mk
<./spell.mk

TGT=dfopt

all:V: $TGT.pdf $TGT.ps supplement.pdf
bib:V: $TGT.bbl
dvi:V: $TGT.dvi
bbl:V: bib

%.bbl: %.aux
	nbibtex $stem

dfopt.dvi: dfopt.bbl code.sty

$TGT.pdf: $TGT.dvi
	dvips -Ppdf -o"|ps2pdf - $target" -pp 1-12 $prereq

supplement.pdf: $TGT.dvi
	dvips -Ppdf -o "|ps2pdf - $target" -pp 13- $prereq

