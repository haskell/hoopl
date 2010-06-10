#	General makefile for Latex stuff

.SUFFIXES: .tib .verb .tex .fig .dvi .ps

MAIN = dfopt

# Styles are in papers/styles
TEXINPUTS := .:../styles//:$(TEXINPUTS)

# Bibliographies are in papers/bibs
BIBINPUTS := .:../bibs//:$(BIBINPUTS)

default: comb1.tex iterf.tex pairf.tex dg.tex  cprop.tex
	[ -r "$(MAIN)du.tex" ] && chmod +w $(MAIN)du.tex
	./defuse < $(MAIN).tex > $(MAIN)du.tex
	chmod -w $(MAIN)du.tex
	latex $(MAIN).tex
#	bibtex $(MAIN)
	latex $(MAIN).tex
	latex $(MAIN).tex
	dvips -f -P pdf < $(MAIN).dvi > $(MAIN).ps
	ps2pdf $(MAIN).ps



esc:
	latex escMeets.tex
	bibtex escMeets
	dvips -f < escMeets.dvi > escMeets.ps

bib:
	bibtex $(MAIN)

pdf:
	latex $(MAIN).tex
	bibtex $(MAIN)
	latex $(MAIN).tex
	pdflatex $(MAIN).tex

ps:
	latex $(MAIN).tex
	bibtex $(MAIN)
	latex $(MAIN).tex
	latex $(MAIN).tex
	dvips -t a4 $(MAIN).dvi -o $(MAIN).ps

clean-ps:
	clean-ps imp*.ps

HOOPL=../src/Compiler/Hoopl

comb1.tex iterf.tex pairf.tex: ./xsource $(HOOPL)/Combinators.hs
	lua ./xsource $(HOOPL)/Combinators.hs

dg.tex: ./xsource $(HOOPL)/Dataflow.hs
	lua ./xsource $(HOOPL)/Dataflow.hs

CLIENT=../testing
CPROPS=$(CLIENT)/ConstProp.hs $(CLIENT)/Simplify.hs $(CLIENT)/Test.hs

cprop.tex: ./xsource $(CPROPS)
	lua ./xsource $(CPROPS)

