# One of these two files will have been generated

.PHONY: all

all: 
	dune build -p rocq-equations,rocq-equations-examples @install

install:
	dune install rocq-equations rocq-equations-examples

.PHONY: install

test-suite:
	dune build -p rocq-equations,rocq-equations-examples,rocq-equations-tests

.PHONY: test-suite

clean:
	dune clean
	
siteexamples: examples/*.glob
	sh siteexamples.sh

doc: html
	mkdir -p html/api && ocamldoc -html -d html/api \
		`ocamlfind query -r rocq-runtime.lib rocq-runtime.kernel rocq-runtime.tactics rocq-runtime.proofs \
			rocq-runtime.toplevel rocq-runtime.ltac rocq-runtime.plugins.extraction -i-format` \
	  -I src src/*.ml

toplevel: src/equations_plugin.cma bytefiles
	"$(OCAMLFIND)" ocamlc -linkpkg -linkall -g $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-package rocq-runtime.toplevel,rocq-runtime.plugins.extraction \
	  $< $(COQLIB)/toplevel/coqtop_bin.ml -o coqtop_equations

ci-dune:
	dune build -p rocq-equations,rocq-equations-examples,rocq-equations-tests
	dune build -p rocq-equations,rocq-equations-examples @install
	dune install rocq-equations rocq-equations-examples

ci-hott:
	opam install -j 2 -y coq-hott.dev
	test -f Makefile.hott && $(MAKE) -f Makefile.hott all
	$(MAKE) -f Makefile.hott install
	$(MAKE) -f Makefile.hott uninstall
	
.PHONY: ci-dune ci-hott
