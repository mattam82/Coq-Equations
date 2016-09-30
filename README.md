# Equations
A plugin for dependent pattern-matching.

Copyright 2009-2016 Matthieu Sozeau `matthieu.sozeau@inria.fr`.
Distributed under the terms of the GNU Lesser General Public
License Version 2.1 (see `LICENSE` for details).

## Install with OPAM
This package is available on [OPAM](http://opam.ocaml.org/).
Activate the [Coq repository](https://github.com/coq/opam-coq-archive):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-equations

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

To get the development version of Equations, activate the repository:

    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

## Install by hand
Alternatively, to compile Equations, simply run:

    coq_makefile -f _CoqProject -o Makefile
    make

in the toplevel directory, with `coqc` and `ocamlc` in your path.

Then add the paths to your `.coqrc`:

    Add ML Path "/Users/mat/research/coq/equations/src".
    Add Rec LoadPath "/Users/mat/research/coq/equations/theories" as Equations.

Or install it:

    make install

As usual, you will need to run this command with the appropriate privileges
if the version of Coq you are using is installed system-wide, rather than
in your own directory. E.g. on Ubuntu, you would prefix the command with
`sudo` and then enter your user account password when prompted.

## Documentation
A preliminary documentation is available in `doc/` and
some examples in `test-suite/` and `examples/`.
