# One of these two files will have been generated

.PHONY: all default

all: Makefile.coq
	$(MAKE) -f Makefile.coq
	test -f Makefile.hott && $(MAKE) -f Makefile.hott || true

install: Makefile.coq
	$(MAKE) -f Makefile.coq install
	test -f Makefile.hott && $(MAKE) -f Makefile.hott install || true

makefiles: test-suite/Makefile examples/Makefile

clean-makefiles:
	rm -f test-suite/Makefile examples/Makefile

test-suite/Makefile: test-suite/_CoqProject
	cd test-suite && coq_makefile -f _CoqProject -o Makefile

examples/Makefile: examples/_CoqProject
	cd examples && coq_makefile -f _CoqProject -o Makefile

pre-all:: makefiles

# Ensure we make the bytecode version as well
post-all:: bytefiles

clean-examples: makefiles
	cd examples && $(MAKE) clean

clean-test-suite: makefiles
	cd test-suite && $(MAKE) clean

test-suite: makefiles all
	cd test-suite && $(MAKE)

.PHONY: test-suite

examples: examples/Makefile all
	cd examples && $(MAKE)

.PHONY: examples

clean:: clean-makefiles makefiles clean-examples clean-test-suite

siteexamples: examples/*.glob
	sh siteexamples.sh

doc: html
	mkdir -p html/api && ocamldoc -html -d html/api \
		`ocamlfind query -r coq.intf coq.kernel coq.tactics coq.proofs \
												coq.toplevel coq.ltac coq.plugins.extraction -i-format` \
	  -rectypes -I src src/*.ml

toplevel: src/equations_plugin.cma bytefiles
	"$(OCAMLFIND)" ocamlc -linkpkg -linkall -g $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-package coq.toplevel,coq.plugins.extraction \
	  $< $(COQLIB)/toplevel/coqtop_bin.ml -o coqtop_equations

dune:
	dune build

ci-dune:dune

ci-hott:
	test -f Makefile.hott && $(MAKE) -f Makefile.hott all install
	
ci-local:
	$(MAKE) -f Makefile.coq all install test-suite examples
	
.PHONY: ci-dune ci-hott ci-local