From Equations Require Import Equations DepElimDec HSets.
(* Unset Equations OCaml Splitting. *)
Set Universe Polymorphism.
Require Import Relations.

(** Switch to an equality in Type *)
Require Import ConstantsType.

Set Warnings "-notation-overridden".
Import Id_Notations.
Set Warnings "+notation-overridden".

Derive Signature for Id.



Check (_ : HSet nat).

Set Printing Universes.
(* Equations test_k (x : nat) (r : x = x) : r = r := *)
(*   test_k x id_refl := id_refl. *)


Equations foo (A : Type) (x : A) : A :=
foo A x := x.
