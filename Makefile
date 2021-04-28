# One of these two files will have been generated

.PHONY: all default makefiles clean-makefiles

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

clean: clean-makefiles makefiles
	$(MAKE) -f Makefile.coq clean
	test -f Makefile.hott && make -f Makefile.hott clean || true
	$(MAKE) clean-examples clean-test-suite

siteexamples: examples/*.glob
	sh siteexamples.sh

doc: html
	mkdir -p html/api && ocamldoc -html -d html/api \
		`ocamlfind query -r coq-core.lib coq-core.kernel coq-core.tactics coq-core.proofs \
			coq-core.toplevel coq-core.ltac coq-core.plugins.extraction -i-format` \
	  -rectypes -I src src/*.ml

toplevel: src/equations_plugin.cma bytefiles
	"$(OCAMLFIND)" ocamlc -linkpkg -linkall -g $(CAMLDEBUG) $(CAMLFLAGS) $(CAMLPKGS) \
		-package coq-core.toplevel,coq-core.plugins.extraction \
	  $< $(COQLIB)/toplevel/coqtop_bin.ml -o coqtop_equations

dune:-
	dune build

ci-dune:
	opam install -j 2 -y coq-hott.8.13 --ignore-constraints-on=coq
	dune build

ci-hott:
	opam install -j 2 -y coq-hott.8.13 --ignore-constraints-on=coq
	test -f Makefile.hott && $(MAKE) -f Makefile.hott all
	$(MAKE) -f Makefile.hott install
	$(MAKE) -f Makefile.hott uninstall
	
ci-local:
	$(MAKE) -f Makefile.coq all 
	$(MAKE) test-suite examples
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.coq uninstall
	
ci: ci-local

.PHONY: ci-dune ci-hott ci-local