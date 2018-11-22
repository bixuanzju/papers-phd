
MAIN = paper

all: $(MAIN).pdf

$(MAIN).pdf: paper.tex $(wildcard sections/*.tex) paper.bib paper_utility.tex
	@latexmk -pdf $(@:.pdf=.tex)

long: $(wildcard sections/*.tex) paper.bib paper_utility.tex
	@latexmk -jobname=paper_long -pdf -pdflatex='pdflatex %O -interaction=nonstopmode -synctex=1 "\newcommand*{\submitoption}{} \input{%S}"' $(MAIN)

submit: all long

clean:
	@latexmk -c
	@rm -Rf auto/ sections/auto/ upload/ coq/ latex.out/ *.out *.log *.gz *.blg *.fls *.aux *.bbl *.fdb_latexmk

.PHONY: all clean submit long FORCE
