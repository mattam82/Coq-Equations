COQDOCOPTS=--utf8 -g --interpolate -coqlib http://coq.inria.fr/stdlib/
COQOPTS=
TARGETS=intro.vo intro.coq.tex noconf.vo noconf.coq.tex Below.vo Below.coq.tex wf.vo wf.coq.tex equations.pdf intro.html
COQBIN=~/research/coq/trunk/bin/


all: ${TARGETS}

%.vo: %.v
	${COQBIN}coqc ${COQOPTS} $<

%.coq.tex: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --body-only --latex --glob-from ${<:.vo=.glob} -o $@ ${<:.vo=.v}
	rm coqdoc.sty

%.html: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --html --glob-from ${<:.vo=.glob} -o $@ ${<:.vo=.v}
	cp ~/research/publication/styles/coqdoc.css .

%.pdf: %.tex
	pdflatex $<

clean:
	rm -f ${TARGETS}

equations.pdf: intro.coq.tex