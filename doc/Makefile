COQDOCOPTS=--utf8 --body-only --latex -g --interpolate
COQOPTS=
TARGETS=intro.vo intro.tex
COQBIN=~/research/coq/trunk/bin/

all: ${TARGETS}

%.vo: %.v
	${COQBIN}coqc ${COQOPTS} $<

%.tex: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --glob-from ${<:.vo=.glob} -o ${<:.vo=.tex} ${<:.vo=.v}
	rm coqdoc.sty

clean:
	rm -f ${TARGETS}