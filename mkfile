<./latex.mk
<./spell.mk
<./bbl.$USER.mk


TGT=dfopt

all:V: $TGT.pdf $TGT.ps supplement.pdf
bib:V: $TGT.bbl
dvi:V: $TGT.dvi
bbl:V: bib

dfopt.dvi: dfopt.bbl code.sty timestamp.tex

$TGT.pdf: $TGT.dvi
	dvips -Ppdf -o"|ps2pdf - $target" -pp 1-12 $prereq

supplement.pdf: $TGT.dvi
	dvips -Ppdf -o "|ps2pdf - $target" -pp 13- $prereq

timestamp.tex: $TGT.tex
	date=`stat -c "%y" $prereq`
	signature=""
	if [ -x $HOME/bin/md5words ]; then
          signature=" [MD5: \\mbox{`md5words $prereq`}]"
	fi
	date -d "$date" "+\\rlap{\\textbf{\\uppercase{%A} %l:%M %p$signature}}" > $target


