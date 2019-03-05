Set Warnings "-notation-overridden".

Set Universe Polymorphism.
Require Import Relations.
(** Switch to an equality in Type *)
Require Import Equations.Init.
Require Import Equations.Type.All.

Derive Signature for Id.

Definition nathset := _ : HSet nat.

Set Printing Universes.
(* Equations test_k (x : nat) (r : x = x) : r = r := *)
(*   test_k x id_refl := id_refl. *)


Equations foo (A : Type) (x : A) : A :=
foo A x := x.


Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature for fin.

Derive NoConfusion for nat.

Set Universe Minimization ToSet.

Equations finp {n} (f : fin (S n)) : unit + fin n :=
  finp fz := inl tt;
  finp (fs f) := inr f.
