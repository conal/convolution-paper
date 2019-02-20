outdir=out

paper = convolution

icfp = $(outdir)/$(paper)-icfp
extended = $(outdir)/$(paper)-extended
extended-anon = $(outdir)/$(paper)-extended-anon

all: $(extended).pdf
all: $(icfp).pdf
all: $(extended-anon).pdf

icfp: $(icfp).pdf
extended: $(extended).pdf
extended-anon: $(extended-anon).pdf

# all += $(icfp).pdf
# all += $(extended).pdf
# all += $(extended-anon).pdf

all: $(all)

# opaper = $(outdir)/$(paper)

# # Doesn't work
# .PRECIOUS: $(outdir)/%.tex $(outdir)/%.pdf

.PRECIOUS: out/convolution.tex out/convolution.pdf
.PRECIOUS: out/was1.tex out/was1.pdf
.PRECIOUS: out/was2.tex out/was2.pdf
.PRECIOUS: out/was3.tex out/was3.pdf
.PRECIOUS: $(icfp).tex $(icfp).pdf
.PRECIOUS: $(extended).tex $(extended).pdf
.PRECIOUS: $(extended-anon).tex $(extended-anon).pdf

latex=latexmk -pdf
latex+= -outdir=${outdir}
# latex+= -synctex=1
latex+= -halt-on-error
# # Preview continuously
# latex+= -pvc

%.pdf: %.tex bib.bib Makefile
	$(latex) $*.tex
	touch $@

# The previous rule always ran, and I didn't know why. Passing "-d" (debug) to
# make, I see that it's because the PDFs are not getting updated by latexmk,
# so their prerequisites stay newer. Workaround: touch the PDF.

figures: $(figures)

texdeps = formatting.fmt Makefile

$(icfp).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=icfp --set=anonymous -o $*.tex $(paper).lhs

$(extended).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=extended -o $*.tex $(paper).lhs

$(extended-anon).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=extended --set=anonymous -o $*.tex $(paper).lhs

showpdf=skim

%.see: %.pdf
	${showpdf} $<

see: $(extended).see

SHELL = bash

clean:
	rm -f ${outdir}/*

TAGS: *.tex *.lhs *.bib src/*.hs src/*.inc
	etags $^

web: web-token

web-token: $(short).pdf $(extended).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(paper)
	touch web-token
