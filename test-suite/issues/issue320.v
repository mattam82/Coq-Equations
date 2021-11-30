Inductive Vec f : nat -> Type :=
    | vnil : Vec f 0
    | vcons : forall n, f n -> Vec f n -> Vec f (S n).

From Equations Require Import Equations.

Derive Signature for Vec.

From Coq Require Fin.
Notation fin := Fin.t.

Set Equations Transparent.
Derive Signature for Fin.t.

Equations fin_to_nat {n : nat} (i : fin n) : nat :=
 | Fin.F1 := 0;
 | Fin.FS f := S (fin_to_nat f).

Coercion fin_to_nat : Fin.t >-> nat.

Equations fin_pred {n} (m : fin (S n)) (H : S n <> S m) : fin n :=
  fin_pred (n:=0) Fin.F1 H with H eq_refl := {};
  fin_pred (n:=S n) Fin.F1 H := Fin.F1;
  fin_pred (n:=0) (Fin.FS !) H ;
  fin_pred (n:=S n) (Fin.FS f) H := Fin.FS (fin_pred f _).

Lemma fin_pred_to_nat {n} (m : fin (S n)) (H : S n <> S m) : m = fin_pred m H :> nat.
Proof.
  funelim (fin_pred m H). cbn. reflexivity.
  cbn. now f_equal.
Qed.

Lemma neq_sym {A} {x y : A} : x <> y -> y <> x.
Proof.
  intros heq heq'. apply heq. now symmetry.
Qed.

Equations take_right_S {f n} (m: fin n) (v: Vec f (S n)) : Vec f (S m) by struct v :=
take_right_S m (vcons (S n1) f1 v) with eq_dec (S m) (S n1) =>
  take_right_S m (vcons (S n1) f1 v) (right e) := _ (take_right_S (fin_pred m (neq_sym e)) v) ;
  take_right_S m (vcons (S n1) f1 v) (left e) :=
    eq_rect _ (fun n => Vec f n) v _ (eq_sym e).
Next Obligation.
  intros.
  rewrite <- fin_pred_to_nat in x. exact x.
Defined.

Fail Equations take_right_S_fail {f n} (m: fin n) (v: Vec f (S n)) : Vec f (S m) by struct v :=
take_right_S_fail m (vcons (S n1) f1 v) with eq_dec (S m) (S n1) =>
  take_right_S_fail m (vcons (S n1) f1 v) (right e) := _ (take_right_S_fail (fin_pred m (neq_sym e)) v) ;
  take_right_S_fail m (vcons (S n1) f1 v) (left eq_refl) := v.
