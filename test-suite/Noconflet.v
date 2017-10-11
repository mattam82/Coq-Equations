Require Import Equations.

Derive NoConfusion for vector.

Inductive foo (A : Type) : nat -> bool -> Set :=
| fool n : foo A n true
| foor : foo A 0 false.

Derive NoConfusion for foo.

Inductive foolet (A : Type) (B := A) : nat -> bool -> Set :=
| fooletl n : foolet A n true
| fooletr : foolet A 0 false.

Derive NoConfusion for foolet.

(** elim vs destruct bug on foolet *)

(* Next Obligation. *)
(*   intros. destruct_sigma b. elim b. *)
(*   destruct b. solve_ *)
(*                 destruct pr1. simpl. simpl in *. *)
(*   (* Bug in Coq: destruct pr2 *) *)
(*   elim pr2. simpl. intros; auto. *)
(*   simpl. auto. *)
(* Defined. *)
