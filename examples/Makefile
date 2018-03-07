#vfiles := HoTT_light.v RoseTree.v graph_complete.v STLC.v polynomials.v string_matching.v nested_mut_rec.v MoreDep.v general_recursion.v Basics.v
vfiles := Basics.v

texfiles := $(vfiles:.v=.tex)

COQC?="$(COQBIN)coqc"
COQFLAGS = -w "+compatibility-notation" -I ../src -R ../theories Equations
COQDOC?="$(COQBIN)coqdoc"

all: $(texfiles)

clean:
	rm -f $(vfiles:.v=.vo)
	rm -f $(vfiles:.v=.glob)
	rm -f $(vfiles:.v=.tex)

$(vfiles:.v=.vo): %.vo: %.v
	$(COQC) $(COQFLAGS) $<

graph_complete.vo: HoTT_light.vo

$(vfiles:.v=.tex): %.tex: %.vo
	$(COQDOC) --latex --interpolate --parse-comments ${<:.vo=.v}

