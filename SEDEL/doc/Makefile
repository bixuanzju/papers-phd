
OTT_LOC    = ../spec

OTT_OPTS  = -tex_show_meta false
OTT_FILES  = $(OTT_LOC)/*.ott

MAIN = paper

SCRIPT = script

RULESFILE = ott-rules.tex

AUTOGEN = sections/typesystem.mng appendix.mng


WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

all: $(MAIN).pdf

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


clean:
	@latexmk -c

.PHONY: all clean
