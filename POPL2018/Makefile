
MAIN = paper

all: $(MAIN).pdf

$(MAIN).pdf: $(wildcard sections/*.tex) paper.bib paper_utility.tex
	@latexmk -pdf $(@:.pdf=.tex)

long: $(wildcard sections/*.tex) paper.bib paper_utility.tex
	@latexmk -jobname=paper_long -pdf -pdflatex='pdflatex %O -interaction=nonstopmode -synctex=1 "\newcommand*{\submitoption}{} \input{%S}"' $(MAIN)

submit: all long
	rm -Rf coq && mkdir -p coq
	rsync --relative --files-from submit.txt ../coq coq
	tar zcf bundle.tar.gz paper_long.pdf coq
	mkdir -p upload
	mv bundle.tar.gz $(MAIN).pdf upload/

clean:
	@rm -f paper.pdf paper_long.pdf *.loe *.bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	@rm -Rf auto/ sections/auto/ upload/ coq/

.PHONY: all clean submit long
