Require Import Program. 
Require Import Equations Bvector List.
Require Import Relations.
Require Import DepElimDec.

Require Import Arith Wf_nat.
Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : Below.
Ltac rec ::= rec_wf_eqns.

Definition measure {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Definition f91_rel : relation nat :=
  measure (fun x => 101 - x) lt.

Instance gt_bound_wf : WellFounded f91_rel.
Proof. red. red. intros.
  Admitted.

Equations(noind) f91 n : { m : nat | if le_lt_dec n 100 then m = 91 else m = n - 10 } :=
f91 n by rec n f91_rel :=
f91 n with le_lt_dec n 100 := {
  | left H := exist _ (proj1_sig (f91 (proj1_sig (f91 (n + 11))))) _ ;
  | right H := exist _ (n - 10) _ }.

Require Import Omega.

Next Obligation. intros. apply f91. do 2 red. try omega. Defined.
Next Obligation. intros. apply f91. destruct f91_comp_proj. simpl. do 2 red.
  destruct_call le_lt_dec. subst. omega. subst. omega.
Defined.
  
Next Obligation. destruct le_lt_dec. intros. destruct_call f91_comp_proj. simpl. 
  destruct_call f91_comp_proj. simpl in *. destruct le_lt_dec. subst. simpl in y. auto.
  subst x0. destruct le_lt_dec. auto.
  subst x. simpl. omega.

  elimtype False. omega.
Qed.

Next Obligation. destruct le_lt_dec. intros. omega. omega. Defined.

(* Next Obligation.  *)
(* Proof. intros. *)
(*   rec_wf_rel n IH f91_rel. *)
(*   simp f91. constructor. destruct le_lt_dec. constructor. intros. apply IH. *)
(*   do 2 red; omega. *)
(*   apply IH. do 2 red; omega. *)
(*   apply IH. do 2 red. destruct_call f91. simpl proj1_sig.  *)
(*   destruct le_lt_dec; subst; omega. *)
(*   apply IH. *)
(*   simp f91. *)
(* Defined. *)
