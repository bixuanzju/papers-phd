MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(wildcard sections/*.tex) $(wildcard sections/*.lhs) $(wildcard sections/*.ott) $(MAIN).tex $(MAIN).bib
	make -C sections
	pdflatex $(@:.pdf=.tex)
	bibtex $(@:.pdf=)
	pdflatex $(@:.pdf=.tex)
	pdflatex $(@:.pdf=.tex)

clean:
	touch $(MAIN).tex
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).synctex.gz $(MAIN).blg texput.log

distclean: clean
	make -C sections clean
	rm -f $(MAIN).pdf $(MAIN).bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	rm -f upload.zip

package: $(MAIN).pdf
	zip upload.zip main.tex main.bib llncs.cls splncs03.bst mathpartir.sty mylhs2tex.sty \
	  sections/expcore.ott.tex sections/otthelper.tex sections/introduction.tex \
	  sections/overview.tex sections/explicitcore.tex sections/fullreduct.tex \
	  sections/related.tex sections/conclusion.tex

.PHONY: all clean distclean
