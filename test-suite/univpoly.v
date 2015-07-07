Require Import Equations.

Set Universe Polymorphism.

(* Move fix_proto to poly version *)
Equations(noind) id (A : Type) (a : A) : A :=
id A x := x.



