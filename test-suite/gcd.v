From Equations Require Import Equations.
Require Import Relations.
Require Import Arith Lia.
Set Keyed Unification.

Ltac subst_lets :=
  repeat match goal with
  | id := _ |- _ => subst id
  end.

Hint Extern 5 => 
  simpl; subst_lets; lia : Below.

Obligation Tactic := Equations.CoreTactics.equations_simpl; try typeclasses eauto with Below.

Equations gcd (x y : nat) : nat by wf (x + y) lt :=
gcd 0 x := x ;
gcd x 0 := x ;
gcd x y with gt_eq_gt_dec x y := {
  | inleft (left ygtx) := gcd x (y - x) ;
  | inleft (right refl) := x ;
  | inright xgty := gcd (x - y) y }.
Transparent gcd.
Eval compute in gcd 18 84.

Require Import ExtrOcamlBasic.
(* Extraction gcd. *)
(* Extraction gcd_unfold. *)

Lemma gcd_same x : gcd x x = x.
Proof.
  funelim (gcd x x); now (try (exfalso; lia)).
Qed.

Lemma gcd_spec0 a : gcd a 0 = a.
Proof.
  funelim (gcd a 0); reflexivity.
Qed.
Hint Rewrite gcd_spec0 : gcd.

Lemma mod_minus a b : b <> 0 -> b < a -> (a - b) mod b = a mod b.
Proof.
  intros.
  replace a with ((a - b) + b) at 2 by lia.
  rewrite <- Nat.add_mod_idemp_r; auto.
  rewrite Nat.mod_same; auto.
Qed.

Lemma gcd_spec1 a b: 0 <> b -> gcd a b = gcd (Nat.modulo a b) b.
Proof.
  funelim (gcd a b); intros. rewrite Nat.mod_0_l; auto. simp gcd.
  simpl in H.
  rewrite (Nat.mod_small (S n) (S n0)); auto.
  set(x := S n) in *. set (y := S n0) in *.
  change (n0 - n) with (y - x).
  rewrite gcd_equation_3. rewrite Heq. simpl. reflexivity.
  rewrite e. rewrite Nat.mod_same; auto.
  rewrite H; auto.
  rewrite mod_minus; auto.
Qed.
