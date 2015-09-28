Require Import Equations.Equations.

Set Universe Polymorphism.

(* Move fix_proto to poly version *)
Equations(noind) id (A : Type) (a : A) : A :=
id A x := x.
Set Printing Universes.
(* Move fix_proto to poly version *)
Equations foo (A : _) (a : A) : A :=

Equations(nocomp) foo' (A : _) (x : A) : A :=
foo' A x := x.
