#	General makefile for Latex stuff

.SUFFIXES: .tib .verb .tex .fig .dvi .ps

MAIN = dfopt

# Styles are in papers/styles
TEXINPUTS := .:../styles//:$(TEXINPUTS)

# Bibliographies are in papers/bibs
BIBINPUTS := .:../bibs//:$(BIBINPUTS)

default:
	latex $(MAIN).tex
	bibtex $(MAIN)
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
