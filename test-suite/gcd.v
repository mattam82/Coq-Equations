From Equations Require Import Equations.
Require Import Relations.

Definition gcd_order (p : nat * nat) : nat := let (x,y) := p in x+y.


Definition measure {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Definition gcd_rel : relation (nat * nat) :=
  MR lt gcd_order.

Instance gt_bound_wf : WellFounded gcd_rel.
Proof. red. apply measure_wf. apply Wf_nat.lt_wf. Defined.

Require Import Omega.

Ltac subst_all :=
  repeat match goal with
  | id := _ |- _ => subst id
  end.
Hint Extern 5 => 
  unfold gcd_rel, gcd_order, MR; simpl; subst_all; omega : Below.


Equations gcd (p : nat * nat) : nat by rec p gcd_rel :=
gcd (pair 0 _) := 0 ;
gcd (pair _ 0) := 0 ;
gcd (pair (S x) (S y)) with gt_eq_gt_dec x y := {
  | inleft (left ygtx) := gcd (S x, y - x) ;
  | inleft (right refl) := S x ;
  | inright xgty := gcd (x - y, S y) }.

Equations gcd' (p : nat * nat) : nat
  by rec p gcd_rel :=
gcd' (pair 0 _) := 0 ;
gcd' (pair _ 0) := 0 ;
gcd' (pair x y) with gt_eq_gt_dec x y := {
  | inleft (left ygtx) := gcd' (x, y - x) ;
  | inleft (right refl) := x ;
  | inright xgty := gcd' (x - y, y) }.

(* Extraction gcd. *)
(* Extraction gcd_unfold. *)

Lemma gcd_ref x : gcd (x,x) = x.
Proof.
  funelim (gcd (x, x)); now (try (exfalso; omega)). 
Qed.

(* Module Function.     *)
(* Require Import Recdef. *)
(* Function gcd (p : nat * nat) {measure gcd_order p} : nat := *)
(*  match p with *)
(*    | (0,_) => 0 *)
(*    | (_,0) => 0 *)
(*    | (x,y) => match gt_eq_gt_dec x y with *)
(*                 | inleft (left _) => gcd (x, y-x) *)
(*                 | inleft (right _) => x *)
(*                 | inright xgty => gcd (x-y, y) *)
(*               end *)
(*  end. *)
(* - unfold gcd_order ; intros ; omega. *)
(* - unfold gcd_order ; intros ; omega. *)
(* Defined. *)

(* Lemma gcd_ref x : gcd (x,x) = x. *)
(* Proof. *)
(*   functional induction (gcd (x, x)). Abort. *)

(* End Function. *)