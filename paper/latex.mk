LATEX=latex
DVIPS=dvips

%.dvi:  %.tex
	$LATEX '\scrollmode \input '"$stem"
	ltxcount=3
	while egrep -s 'Rerun (LaTeX|to get cross-references right|to get citations correct)' $stem.log &&
	      [ $ltxcount -gt 0 ]
	do
	  $LATEX '\scrollmode \input '"$stem"
	  ltxcount=`expr $ltxcount - 1`
	done

%.ps:	%.dvi
	$DVIPS -Ppdf -o $target $stem.dvi
%.pdf:	%.dvi
	$DVIPS -Ppdf -o"| ps2pdf13 - $target" $prereq

