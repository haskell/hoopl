%.bbl: %.aux
	nbibtex $stem

%.bib: %.aux
	nbibtex -o $target -bib $stem

