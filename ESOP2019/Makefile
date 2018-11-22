OTT_LOC    = ./spec

OTT_OPTS  =  -tex_wrap false -tex_show_meta false

OTT_FILES  = $(OTT_LOC)/*.ott

MAIN = paper

SCRIPT = script

OTT_GEN = ott-rules.tex

AUTOGEN = Sources/typesystem.mng Sources/coherence.mng Sources/related.mng Sources/translation.mng

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

SCRIPT = script

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(wildcard ./*.tex) $(wildcard Sources/*.tex) $(AUTOGEN) $(OTT_FILES)
	@ruby $(SCRIPT).rb
	@latexmk $(@:.pdf=.tex)


test: $(AUTOGEN) $(OTT_FILES)
	@ruby $(SCRIPT).rb
	@tectonic $(MAIN).tex


$(OTT_GEN): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

%.mng: %.tex $(OTT_GEN)
	ott $(OTT_OPTS) -tex_filter $*.tex $*.mng $(OTT_FILES)
	@perl -pi -e 'print $(WARN_MSG) if $$. == 1' $@

clean:
	@latexmk -C

.PHONY: all clean
