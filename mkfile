<./latex.mk

TGT=dfopt

all:V: $TGT.pdf $TGT.ps
bib:V: $TGT.bbl
dvi:V: $TGT.dvi
bbl:V: bib

%.bbl: %.aux
	nbibtex $stem

dfopt.dvi: logic.tex dfopt.bbl code.sty

