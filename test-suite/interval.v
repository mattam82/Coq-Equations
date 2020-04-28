From Equations Require Import Equations.
Require Import List Arith Lia.
Import ListNotations.

Set Keyed Unification.
Set Equations Transparent.
Equations? interval x y : list nat by wf (y - x) lt :=
  interval x y with lt_dec x y :=
    { | left ltxy =>  x :: interval (S x) y;
      | right nltxy => [] }.
Proof. lia. Defined.

Lemma interval_empty x : interval x x = [].
Proof. funelim (interval x x). clear Heq; now apply Nat.lt_irrefl in l. reflexivity. Qed.

Lemma interval_large x y : ~ x < y -> interval x y = [].
Proof. funelim (interval x y); clear Heq; intros; now try lia. Qed.

Lemma interval_trans x y z : x < y < z -> interval x y ++ interval y z = interval x z.
Proof.
  revert z; funelim (interval x y); intros z H'; clear Heq.
  - simpl.
    destruct (lt_dec (S x) y); simpl.
    rewrite H; try lia.
    rewrite (interval_equation_1 x z).
    destruct lt_dec; simpl; trivial. elim n. lia.
    assert (y = S x) as -> by lia. rewrite interval_empty. simpl.
    rewrite (interval_equation_1 x z). destruct (lt_dec x z); trivial. elim n0; lia.
  - elim n; lia.
Qed.
