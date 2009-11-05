COQDOCOPTS=--utf8 --body-only --latex -g --interpolate
COQOPTS=
TARGETS=intro.vo intro.tex equations.pdf
COQBIN=~/research/coq/trunk/bin/

all: ${TARGETS}

%.vo: %.v
	${COQBIN}coqc ${COQOPTS} $<

%.tex: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --glob-from ${<:.vo=.glob} -o ${<:.vo=.tex} ${<:.vo=.v}
	rm coqdoc.sty

equations.tex: intro.tex

%.pdf: %.tex
	pdflatex $<

clean:
	rm -f ${TARGETS}