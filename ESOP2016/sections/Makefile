OTT_FILES = expcore.ott srclang.ott cocpts.ott
OTT_OPTS  = -tex_show_meta false
TARGETS   = overview.tex explicitcore.tex appendix.tex examples.tex recursion.tex datatypes.tex discussion.tex otthelper.tex conclusion.tex related.tex

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

all: $(TARGETS) expcore.ott.tex

# Hack to use mathpartir for ott
expcore.ott.tex: $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^
	@perl -0pi -e 's/\{%(\n|\r\n)\\ottpremise/{%\n/g' $@
	@perl -pi -e 's/^\\ottpremise/\\\\ /g' $@
	@perl -pi -e 's/^(.*\\ottlinebreak.*)$$/\\\\$$1/g' $@

%.mng.tex: %.lhs
	lhs2TeX -o $@ $^

%.tex: %.mng.tex $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)
	@perl -pi -e 'print $(WARN_MSG) if $$. == 1' $@

.PHONY: all clean
clean:
	rm -f *.ott.tex $(TARGETS)
