# Equations

A function definition plugin.

Copyright 2009-2017 Matthieu Sozeau `matthieu.sozeau@inria.fr`

Copyright 2015-2017 Cyprien Mangin `cyprien.mangin@m4x.org`

Distributed under the terms of the GNU Lesser General Public
License Version 2.1 (see `LICENSE` for details).

Equations provides a notation for writing programs by dependent 
pattern-matching and (well-founded) recursion
in [Coq](http://coq.inria.fr). It compiles everything down to
eliminators for inductive types, equality and accessibility,
providing a definitional extension to the Coq kernel.

## Documentation

The [reference manual](http://github.com/mattam82/Coq-Equations/tree/master/doc/equations.pdf)
providing an introduction is available along
with [examples](http://github.com/mattam82/Coq-Equations/tree/master/examples).

## Bibliography

Two articles describing the system are available:

- [Equations Reloaded](http://hal.inria.fr/), Cyprien Mangin and
  Matthieu Sozeau (October
  2017). Submitted.
- [Equations: A Dependent Pattern-Matching Compiler](https://link.springer.com/chapter/10.1007/978-3-642-14052-5_29) Matthieu
  Sozeau (2010) 
  In: Kaufmann M., Paulson L.C. (eds) Interactive Theorem
  Proving. ITP 2010. Lecture Notes in Computer Science,
  vol 6172. Springer, Berlin, Heidelberg.
  
## Installation

Below are installation instructions.

### Install with OPAM
This package is available on [OPAM](http://opam.ocaml.org/).
Activate the [Coq repository](https://github.com/coq/opam-coq-archive)
if you didn't do it yet:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-equations

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

To get the development version of Equations, activate the repository:

    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

### Install by hand
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
