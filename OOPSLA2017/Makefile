MAIN = paper

SCRIPT = script

SLIDE = slide

all: $(MAIN).pdf

$(MAIN).pdf: $(wildcard ../examples/*.sl) $(wildcard sections/*.ott) $(wildcard sections/*.tex) $(MAIN).tex paper.bib
	make -C sections
	@ruby $(SCRIPT).rb
	@latexmk -pdf $(@:.pdf=.tex)

slide : $(MAIN).pdf
	@latexmk -pdf $(SLIDE).tex

submit: $(MAIN).pdf
	rm -Rf impl && mkdir -p impl
	rsync --relative --files-from submit.txt ../ impl
	tar zcf bundle.tar.gz impl
	rm -Rf upload && mkdir -p upload
	mv bundle.tar.gz $(MAIN).pdf upload/

clean:
	@rm -f $(MAIN).pdf $(MAIN).bbl $(SLIDE).pdf *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg bundle.tar.gz
	@rm -Rf auto/ sections/auto/ impl upload/

.PHONY: all clean submit
