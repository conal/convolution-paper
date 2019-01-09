targ = convolution

.PRECIOUS: %.tex

default: $(targ).pdf

# dots = $(wildcard figures/*.dot)
# figures = $(addsuffix .pdf, $(basename $(dots)))

#latex=pdflatex
latex=latexmk -pdf -halt-on-error

%.pdf: %.tex bib.bib $(figures) Makefile
	$(latex) $*.tex

figures: $(figures)

%.tex: %.lhs macros.tex formatting.fmt Makefile
	lhs2TeX -o $*.tex $*.lhs

# Cap the size so that LaTeX doesn't choke.
%.pdf: %.dot # Makefile
	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

showpdf=skim

%.see: %.pdf
	${showpdf} $<

see: $(targ).see

# see: $(targ).pdf
# 	${showpdf} $(targ).pdf

SHELL = bash

clean:
	rm -f {$(targ),was1}.{tex,dvi,pdf,aux,bbl,blg,out,log,ptb,fdb_latexmk,fls}

web: web-token

web-token: $(targ).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(targ)
	touch web-token
