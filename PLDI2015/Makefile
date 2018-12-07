#-----------------------------------------------------------------------------
# Programs
#-----------------------------------------------------------------------------
LHS2TEX     := lhs2TeX
PDFLATEX    := pdflatex
LATEX       := latex
BIBTEX      := bibtex
GHCI        := ghci


#-----------------------------------------------------------------------------
# Directories and source files
#-----------------------------------------------------------------------------
MAIN        := Main
MAINTECH    := Main_techmemo
SRCDIR      := src
LHSFILES    := $(wildcard $(SRCDIR)/*.lhs)
TEXFILES    := $(wildcard $(SRCDIR)/*.tex)

#-----------------------------------------------------------------------------
# Flags
#-----------------------------------------------------------------------------
GHCFLAGS      := -Wall -O
LHS2TEX_FLAGS := --poly -s dvipdfm
SPELL         := ispell -d british -t -l -p

all: $(MAIN).dvi
	dvipdf $<
#	ps2pdf $< 

# $(MAINTECH).pdf

#-----------------------------------------------------------------------------
# Pattern rules
#-----------------------------------------------------------------------------

$(MAINTECH).pdf: $(MAINTECH).tex lhs $(TEXFILES) force
	$(PDFLATEX) $<
	if grep -s '^LaTeX Warning: Citation' $(<:.tex=.log); \
	then $(BIBTEX) $(<:.tex=); $(PDFLATEX) $(<); \
	fi
	while grep -s "Warning.*Rerun" $(<:.tex=.log); \
	  do $(PDFLATEX) $<; done;

%.tex : %.lhs force
	[ $(<) ] && ($(LHS2TEX) $(LHS2TEX_FLAGS) $< > $@ || rm -f $@)

%.pdf : %.dvi
	dvipdfm $<

#-----------------------------------------------------------------------------
# Rules
#-----------------------------------------------------------------------------

$(MAIN).dvi: $(MAIN).tex lhs $(TEXFILES) force
	$(LATEX) $(<)
	if grep -s '^LaTeX Warning: Citation' $(<:.tex=.log); \
	then $(BIBTEX) $(<:.tex=); $(LATEX) $(<); \
	fi
	while grep -s "Warning.*Rerun" $(<:.tex=.log); \
	  do $(LATEX) $<; done;

lhs: $(LHSFILES:.lhs=.tex)

ghci: $(file).lhs
	ghci $(file).lhs

spell: $(file).tex
	egrep -v '$\%' $(file).tex | $(spell) $(file).spell | sort | uniq

force:

clean:
	rm -vf $(LHSFILES:.lhs=.tex)
	rm -vf *.pdf
	rm -vf *.dvi
	rm -vf *.aux *.log *.bbl *.blg *.ptb
	rm -rfv auto _region_.tex

.PHONY: ghci spell force clean

