
outdir=out

targ = convolution

otarg = $(outdir)/$(targ)

# # Doesn't work
# .PRECIOUS: $(outdir)/%.tex $(outdir)/%.pdf

.PRECIOUS: out/convolution.tex out/convolution.pdf
.PRECIOUS: out/was1.tex out/was1.pdf
.PRECIOUS: out/was2.tex out/was2.pdf
.PRECIOUS: out/was3.tex out/was3.pdf

default: $(otarg).pdf

# dots = $(wildcard figures/*.dot)
# figures = $(addsuffix .pdf, $(basename $(dots)))

#latex=pdflatex
latex=latexmk -pdf
latex+= -outdir=${outdir}
# latex+= -synctex=1
latex+= -halt-on-error
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

TAGS: *.tex *.lhs *.bib src/*.hs src/*.inc
	etags $^

web: web-token

web-token: $(otarg).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(targ)
	touch web-token
