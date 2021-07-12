vfiles := equations_intro.v
texfiles := equations.tex manual.tex

COQC?="$(COQBIN)coqc"
COQDOC?="$(COQBIN)coqdoc"

.PHONY: all html

all: equations.pdf

equations.pdf: equations.tex $(texfiles) ${vfiles:.v=.tex}
	latexmk -pdf equations

html:
	rm -rf _build
	mkdir _build
	alectryon.py --frontend coq+rst --backend webpage equations_intro.v --output-directory _build/
	cat custom.css >> _build/tango_subtle.min.css

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

