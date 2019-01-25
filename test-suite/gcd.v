From Equations Require Import Equations.
Require Import Relations.
Require Import Omega.

Ltac subst_lets :=
  repeat match goal with
  | id := _ |- _ => subst id
  end.

Hint Extern 5 => 
  unfold MR; simpl; subst_lets; omega : Below.

Obligation Tactic := program_simpl; try typeclasses eauto with Below.

Equations gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 _ := 0 ;
gcd _ 0 := 0 ;
gcd x y with gt_eq_gt_dec x y := {
  | inleft (left ygtx) := gcd x (y - x) ;
  | inleft (right refl) := x ;
  | inright xgty := gcd (x - y) y }.
Transparent gcd.
Eval compute in gcd 18 84.

Require Import ExtrOcamlBasic.
(* Extraction gcd. *)
(* Extraction gcd_unfold. *)

Lemma gcd_ref x : gcd x x = x.
Proof.
  funelim (gcd x x); now (try (exfalso; omega)).
Qed.
