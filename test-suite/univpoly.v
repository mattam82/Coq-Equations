Require Import Equations.Equations.
Set Universe Polymorphism.
Set Implicit Arguments.

(* Move fix_proto to poly version *)
Equations(noind) id (A : Type) (a : A) : A :=
id A x := x.
Set Printing Universes.
(* Move fix_proto to poly version *)
Equations foo (A : _) (a : A) : A :=
foo A a := a.

Equations(nocomp) foo' (A : _) (x : A) : A :=
foo' A x := x.

Equations(nocomp) refl (A : _) (x : A) : x = x :=
refl A x := @eq_refl _ x.

Equations(nocomp) id' {A : Type} (a : A) : A :=
id' _ a := a.

Equations(nocomp noind) foo'' (u : unit) : id' tt = id' tt :=
foo'' tt := _.

