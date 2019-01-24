
outdir=out

targ = convolution

otarg = $(outdir)/$(targ)

.PRECIOUS: $(outdir)/%.tex

default: $(otarg).pdf

# dots = $(wildcard figures/*.dot)
# figures = $(addsuffix .pdf, $(basename $(dots)))

#latex=pdflatex
latex=latexmk -pdf
latex+= -outdir=${outdir} -outdir=${outdir}
# latex+= -halt-on-error
# # Preview continuously
# latex+= -pvc

%.pdf: %.tex bib.bib $(figures) Makefile
	$(latex) $*.tex

figures: $(figures)

$(outdir)/%.tex: %.lhs macros.tex formatting.fmt Makefile
	lhs2TeX -o $@ $*.lhs

# # Figure generation. Cap the size so that LaTeX doesn't choke.
# %.pdf: %.dot # Makefile
# 	dot -Tpdf -Gmargin=0 -Gsize=10,10 $< -o $@

showpdf=skim

%.see: $(outdir)/%.pdf
	${showpdf} $<

see: $(targ).see

# see: $(targ).pdf
# 	${showpdf} $(targ).pdf

SHELL = bash

# clean:
# 	rm -f {$(targ),was1}.{tex,dvi,pdf,aux,bbl,blg,out,log,ptb,fdb_latexmk,fls}

clean:
	rm -f ${outdir}/*

# TAGS:
# 	etags $(targ).lhs src/*.hs

web: web-token

web-token: $(otarg).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(targ)
	touch web-token
