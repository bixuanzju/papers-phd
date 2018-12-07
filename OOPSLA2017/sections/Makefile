OTT_FILES = miniJS.ott fi.ott
OTT_OPTS  = -tex_show_meta false
TARGETS   = applications.tex desugar.tex

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

all: $(TARGETS) miniJS.ott.tex

%.ott.tex: $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^

%.tex: %.mng.tex $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)
	@perl -pi -e 'print $(WARN_MSG) if $$. == 1' $@
