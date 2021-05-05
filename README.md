### **Equations** - a function definition plugin.

[![Build Status](https://github.com/mattam82/Coq-Equations/actions/workflows/build.yml/badge.svg?branch=master&event=push)](https://github.com/mattam82/Coq-Equations/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.3012649.svg)](https://zenodo.org/record/3012649#.XcEydZNKjOQ)
[![Gitter](https://img.shields.io/gitter/room/nwjs/nw.js.svg)](https://gitter.im/coq/Equations)

Copyright 2009-2021 Matthieu Sozeau `matthieu.sozeau@inria.fr`  
Copyright 2015-2018 Cyprien Mangin `cyprien.mangin@m4x.org`

Distributed under the terms of the GNU Lesser General Public License
Version 2.1 or later
(see
[LICENSE](http://github.com/mattam82/Coq-Equations/raw/master/LICENSE)
for details).

Equations provides a notation for writing programs by dependent 
pattern-matching and (well-founded) recursion
in [Coq](http://coq.inria.fr). It compiles everything down to
eliminators for inductive types, equality and accessibility,
providing a definitional extension to the Coq kernel.

## Live demo

Try it now in your browser with [JSCoq](http://mattam82.github.io/Coq-Equations/assets/jsexamples/equations_intro.html)!

## Documentation

- The [reference manual](http://github.com/mattam82/Coq-Equations/raw/master/doc/equations.pdf)
  provides an introduction and a summary of the commands and options.
  This introduction can also be followed interactively with Equations installed:
  [equations_intro.v](http://github.com/mattam82/Coq-Equations/raw/master/doc/equations_intro.v)

- A gallery of [examples](http://mattam82.github.io/Coq-Equations/examples) provides more consequent
  developments using Equations.

## Papers

Two articles describing the system are available:

- [Equations Reloaded](https://www.irif.fr/~sozeau//research/publications/Equations_Reloaded-ICFP19.pdf): 
  High-Level Dependently-Typed Functional Programming and Proving in Coq. Matthieu Sozeau and Cyprien Mangin. 2019. 
  Proc. ACM Program. Lang. 3, ICFP, Article 86 (August 2019), 29 pages. [DOI](https://doi.org/10.1145/3341690).
  See [Equations Reloaded](http://mattam82.github.io/Coq-Equations/equations-reloaded) for associated material, including a VM to run the examples.

- [Equations: A Dependent Pattern-Matching Compiler](https://link.springer.com/chapter/10.1007/978-3-642-14052-5_29) Matthieu
  Sozeau (2010) 
  In: Kaufmann M., Paulson L.C. (eds) Interactive Theorem
  Proving. ITP 2010. Lecture Notes in Computer Science,
  vol 6172. Springer, Berlin, Heidelberg.

We did a case study on a proof of normalization for an hereditary substitution
procedure:

- [Equations for Hereditary Substitution in Leivant's Predicative
SystemF: A Case Study](http://www.irif.fr/~sozeau/research/publications/Equations_for_Hereditary_Substitution_in_Leivants_Predicative_System_F:_a_case_study.pdf)
  Cyprien Mangin and Matthieu Sozeau. 
  In: Proceedings Tenth International Workshop on Logical Frameworks and Meta Languages: Theory and Practice. 
  Volume 185 of EPTCS. May 2015 - LFMTP'15. 

## Installation

The current development version works with Coq 8.8 (branch
[8.8](https://github.com/mattam82/Coq-Equations/tree/8.8)), 
Coq 8.9 (branch
[8.9](https://github.com/mattam82/Coq-Equations/tree/8.9)),
Coq 8.10 (branch
[8.10](https://github.com/mattam82/Coq-Equations/tree/8.10)),
and the current Coq master branch (branch
[master](https://github.com/mattam82/Coq-Equations/tree/master)).

See [releases](https://github.com/mattam82/Coq-Equations/releases) for
sources and official releases.

# Install with OPAM

This package is available on [OPAM](http://opam.ocaml.org/).
Activate the [Coq repository](https://coq.inria.fr/opam-using.html)
if you didn't do it yet:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-equations

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

To get the development version of Equations, activate the repository:

    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

# Install from source

Alternatively, to compile Equations, simply run:

    ./configure.sh
    make

in the toplevel directory, with `coqc` and `ocamlc` in your path.

Optionally, one can build the test-suite or examples:

    make examples test-suite

Then add the paths to your `.coqrc`:

    Add ML Path "/Users/mat/research/coq/equations/src".
    Add Rec LoadPath "/Users/mat/research/coq/equations/theories" as Equations.

Or install it:

    make install

As usual, you will need to run this command with the appropriate privileges
if the version of Coq you are using is installed system-wide, rather than
in your own directory. E.g. on Ubuntu, you would prefix the command with
`sudo` and then enter your user account password when prompted.

## HoTT Variant

The HoTT variant of Equations currently requires a version of Coq master
and a modification of the HoTT library which can be built using:

    ./configure.sh HoTT

This will clone a branch of HoTT and build it in Equations-HoTT, then
one can make Equations and its library using:

    make
