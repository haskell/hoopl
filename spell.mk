%-spell:V: %.nw 
	PATH=/usr/lib/noweb:/usr/local/noweb/lib:$PATH
	markup $prereq | 
	sed -e '/^@begin code/,/^@end code/d' -e '/^@quote/,/@endquote/d' |
	unmarkup |
	strip-tex-markup |
	sed '/^\\begin{verbatim}/,/^\\end{verbatim}/d' |
	# detex -l | spell +okwords.sort | grep -v '[:,&.]' | grep -v '^[0-9A-Z]*$'
	(sed 's/^/*/' $HOME/okwords.txt; sed 's/^/^/') | ispell -t -a | 
	sed '/^[*+]/d;/^$/d;s/[0-9][0-9 ]*[0-9]/9/;s/ *[0-9][0-9]*//' | sort -uf

%-texspell:V: %.tex
	strip-tex-markup $prereq |
	sed -e '/^\\begin{verbatim}/,/^\\end{verbatim}/d'               \
            -e '/^\\begin{code}/,/^\\end{code}/d'                       \
            -e '/^\\begin{smallverbatim}/,/^\\end{smallverbatim}/d'     \
            -e '/^\\begin{smallcode}/,/^\\end{smallcode}/d'             \
            -e '/^\\begin{numberedcode}/,/^\\end{numberedcode}/d'       |
	(sed 's/^/*/' $HOME/okwords.txt; sed 's/^/^/') | ispell -t -a | 
	sed '/^[*+]/d;/^$/d;s/[0-9][0-9 ]*[0-9]/9/;s/ *[0-9][0-9]*//' | sort -uf

