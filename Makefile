paper = convolution

# # breaks arXiv upload
# outdir=out
outdir=.

conf = $(outdir)/$(paper)-conf
long = $(outdir)/$(paper)-long
long-anon = $(outdir)/$(paper)-long-anon

pdf: $(long).pdf
pdf: $(conf).pdf
pdf: $(long-anon).pdf

see: $(long).see
# see: $(conf).see
# see: $(long-anon).see

long: $(long).pdf
conf: $(conf).pdf
long-anon: $(long-anon).pdf

all: conf
all: long
# all: long-anon

all.see: conf.see long.see long-anon.see


# # Doesn't work
# .PRECIOUS: $(outdir)/%.tex $(outdir)/%.pdf

.PRECIOUS: out/convolution.tex out/convolution.pdf
.PRECIOUS: out/was1.tex out/was1.pdf
.PRECIOUS: out/was2.tex out/was2.pdf
.PRECIOUS: out/was3.tex out/was3.pdf
.PRECIOUS: $(conf).tex $(conf).pdf
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

see-stats:
	echo $(stats)

%.pdf: %.tex macros.tex bib.bib Makefile
	$(latex) $*.tex
	touch $@

# The previous rule always ran. Passing "-d" (debug) to make revealed that the
# PDFs were not getting updated by latexmk, so their prerequisites stay newer.
# Workaround: touch the PDF.

texdeps = formatting.fmt Makefile $(stats)

$(conf).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=conf --set=anonymous -o $*.tex $(paper).lhs

$(long).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=long -o $*.tex $(paper).lhs

# --set=draft

$(long-anon).tex: $(paper).lhs $(texdeps)
	lhs2tex --set=long --set=anonymous -o $*.tex $(paper).lhs

showpdf=skim

%.see: %.pdf
	${showpdf} $<

conf.see: $(conf).see
long.see: $(long).see
long-anon.see: $(long-anon).see

pics = $(wildcard test/*.png)

long.zip: $(long).tex $(long).bbl macros.tex $(pics)
	zip $@ $^

SHELL = bash

# clean:
# 	rm -f ${outdir}/*

clean:
	rm -f {$(conf),$(long),$(long-anon)}.{tex,pdf,aux,nav,snm,ptb,log,out,toc,bbl,blg,fdb_latexmk,fls}


TAGS: *.tex *.lhs *.bib src/*.hs src/*.inc
	etags $^

supp = supplemental-material
$(supp): readme.md stack.yaml package.yaml src/*.hs src/*.inc test/*.hs test/gold/*.txt test/wizard.jpg out/convolution-long-anon.pdf
	mkdir -p $(supp)/{src,test}
	grep -vi conal package.yaml > $(supp)/package.yaml
	cp -p stack.yaml readme.md out/convolution-long-anon.pdf $(supp)
	cp -p src/*.hs src/*.inc $(supp)/src
	cp -p test/*.hs test/wizard.jpg $(supp)/test
	cp -rp test/gold $(supp)/test

# Supplemental tarball in progress
tar: supplemental.tar

supplemental.tar: $(supp)
	tar -cvf $@ $(supp)

web: web-token

web-token: $(long).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(paper)
	touch web-token
