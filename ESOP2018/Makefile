OTT_LOC    = ../../spec

OTT_OPTS  = -tex_show_meta false
OTT_FILES  = $(OTT_LOC)/*.ott

MAIN = paper

SCRIPT = script

RULESFILE = ott-rules.tex

AUTOGEN = appendix.mng sections/typesystem.mng sections/algorithm.mng sections/coherence.mng

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

all: $(MAIN).pdf

long: $(MAIN).tex $(wildcard ../../impl/examples/*.sl) $(wildcard sections/*.tex) $(AUTOGEN)
	@ruby $(SCRIPT).rb
	@latexmk -jobname=paper_long -pdf -pdflatex='pdflatex %O -interaction=nonstopmode -synctex=1 "\newcommand*{\submitoption}{} \input{%S}"' $(MAIN)

$(MAIN).pdf: $(MAIN).tex $(wildcard ../../impl/examples/*.sl) $(wildcard sections/*.tex) $(AUTOGEN)
	@ruby $(SCRIPT).rb
	@latexmk -pdf $(@:.pdf=.tex)

$(RULESFILE): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

%.mng: %.tex $(RULESFILE)
	ott -tex_wrap false $(OTT_OPTS) -tex_filter $*.tex $*.mng $(OTT_FILES)
	@perl -pi -e 'print $(WARN_MSG) if $$. == 1' $@
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

clean:
	@rm -f $(MAIN).pdf $(RULESFILE) *.bbl  *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg bundle.tar.gz

.PHONY: all slides clean FORCE
