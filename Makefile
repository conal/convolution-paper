paper = convolution

outdir=out

icfp = $(outdir)/$(paper)-icfp
long = $(outdir)/$(paper)-long
long-anon = $(outdir)/$(paper)-long-anon

pdf: $(long).pdf
# pdf: $(icfp).pdf
# pdf: $(long-anon).pdf

see: $(long).see
# see: $(icfp).see
# see: $(long-anon).see

icfp: $(icfp).pdf
long: $(long).pdf
long-anon: $(long-anon).pdf

# # Doesn't work
# .PRECIOUS: $(outdir)/%.tex $(outdir)/%.pdf

.PRECIOUS: out/convolution.tex out/convolution.pdf
.PRECIOUS: out/was1.tex out/was1.pdf
.PRECIOUS: out/was2.tex out/was2.pdf
.PRECIOUS: out/was3.tex out/was3.pdf
.PRECIOUS: $(icfp).tex $(icfp).pdf
.PRECIOUS: $(long).tex $(long).pdf
.PRECIOUS: $(long-anon).tex $(long-anon).pdf

latex=latexmk -pdf
latex+= -outdir=${outdir}
# latex+= -synctex=1
latex+= -halt-on-error
# # Preview continuously
# latex+= -pvc

stats = $(wildcard test/stats/*.txt)
stats: $(stats)

%.pdf: %.tex bib.bib $(stats) Makefile
	$(latex) $*.tex
	touch $@

# The previous rule always ran. Passing "-d" (debug) to make revealed that the
# PDFs were not getting updated by latexmk, so their prerequisites stay newer.
# Workaround: touch the PDF.

texdeps = formatting.fmt Makefile

$(icfp).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=icfp --set=anonymous -o $*.tex $(paper).lhs

$(long).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=long -o $*.tex $(paper).lhs

$(long-anon).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=long --set=anonymous -o $*.tex $(paper).lhs

showpdf=skim

%.see: %.pdf
	${showpdf} $<

icfp.see: $(icfp).see
long.see: $(long).see
long-anon.see: $(long-anon).see

SHELL = bash

clean:
	rm -f ${outdir}/*

TAGS: *.tex *.lhs *.bib src/*.hs src/*.inc
	etags $^

web: web-token

web-token: $(short).pdf $(long).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(paper)
	touch web-token
