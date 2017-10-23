vfiles := intro.v
texfiles := equations.tex manual.tex

COQC?="$(COQBIN)coqc"
COQDOC?="$(COQBIN)coqdoc"

all: equations.pdf

equations.pdf: equations.tex $(texfiles) ${vfiles:.v=.tex}
	latexmk -pdf equations

clean:
	rm -f $(vfiles:.v=.vo)
	rm -f $(vfiles:.v=.glob)
	rm -f $(vfiles:.v=.tex)
	latexmk -c equations

clean-all: clean
	latexmk -C equations

$(vfiles:.v=.vo): %.vo: %.v
	$(COQC) $<

$(vfiles:.v=.tex): %.tex: %.vo
	$(COQDOC) --latex --body-only --interpolate --parse-comments ${<:.vo=.v}

