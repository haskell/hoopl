<./latex.mk
<./spell.mk
<./bbl.$USER.mk
<./bitly.$USER.mk


LASTPAGE=12  # use this for submission
#LASTPAGE=   

TGT=dfopt

all:V: $TGT.pdf $TGT.ps popl-index.bitly
bib:V: $TGT.bbl
dvi:V: $TGT.dvi
pdf:V: $TGT.pdf
bbl:V: bib

tag:VQ: $TGT.tex
	tag=`$HOME/bin/md5words $prereq | tr -d "'" | tr -cs a-zA-Z0-9 - | sed s/-*$//`
	echo git tag $tag
	git tag $tag

dfopt.dvi: dfopt.bbl code.sty timestamp.tex dfoptdu.tex

$TGT.pdf: $TGT.dvi
	dvips -Ppdf -o"|ps2pdf - $target" -pp 1-$LASTPAGE $prereq

$HOME/www/drop/popl-index.pdf: $TGT.dvi
	dvips -Ppdf -o "|ps2pdf - $target" -pp 13- $prereq

timestamp.tex: $TGT.tex
	date=`stat -c "%y" $prereq`
	signature=""
	if [ -x $HOME/bin/md5words ]; then
          signature=" [MD5: \\mbox{`md5words $prereq`}]"
	fi
	date -d "$date" "+\def\mdfivestamp{\\rlap{\\textbf{\\uppercase{%A} %l:%M %p$signature}}}" > $target



%du.tex:D: defuse %.tex hsprelude
	[ -r "$target" ] && chmod +w $target
	./defuse < $stem.tex > $target
	chmod -w $target

