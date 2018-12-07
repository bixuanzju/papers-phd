MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(wildcard sections/*.tex) $(MAIN).tex
	@latexmk -pdf $(@:.pdf=.tex)

clean:
	touch $(MAIN).tex
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).synctex.gz $(MAIN).blg texput.log

distclean: clean
	make -C sections clean
	rm -f $(MAIN).pdf $(MAIN).bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg

.PHONY: all clean distclean
