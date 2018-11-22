
MAIN = revision

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	@latexmk -pdf $(@:.pdf=.tex)

clean:
	$(RM) *.dvi *.aux *.log *.bbl *.blg *.toc *.out *.fls *.haux *.ptb *.fdb_latexmk *~ comment.cut

distclean: clean
	$(RM) $(MAIN).pdf
