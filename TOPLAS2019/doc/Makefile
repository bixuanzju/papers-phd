OTT_LOC    = ../../ott

DECL_OTT = $(OTT_LOC)/Decl.ott

OTT_OPTS  = -tex_show_meta false
OTT_FILES  = $(DECL_OTT)

MAIN = paper

RULESFILE = ott-rules.tex

AUTOGEN = sections/appendix.mng sections/algorithm.mng sections/exploration.mng sections/typesystem.mng sections/introduction.mng sections/background.mng sections/extension.mng sections/motivation.mng sections/discussion.mng

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

all: $(MAIN).pdf

$(MAIN).pdf: paper.tex $(wildcard sections/*.tex) paper.bib paper_utility.tex $(AUTOGEN)
	@latexmk -pdf $(@:.pdf=.tex)

$(RULESFILE): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^
	@perl -pi -e 'print $(WARN_MSG) if $$. == 1' $@
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

clean:
	@latexmk -c
	@rm -Rf paper.pdf auto/ sections/auto/ upload/ coq/ latex.out/ *.out *.log *.gz *.blg *.fls *.aux *.bbl *.fdb_latexmk

.PHONY: all clean
