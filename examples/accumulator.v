From Equations Require Import Equations.

Require Import List Program.Syntax Arith Lia.

Equations foo (l : list nat) : list nat :=
  foo l := go [] (length l)

  where go (acc : list nat) (n : nat): list nat :=
  go acc 0     := acc;
  go acc (S n) := go (n :: acc) n.

Lemma foo_spec (l : list nat) : Forall (fun x => x < length l) (foo l).
Proof.
  apply (foo_elim (fun l fool => Forall (fun x => x < length l) fool)
        (fun l acc n fool =>
           n <= length l ->
           Forall (fun x => x < length l) acc -> Forall (fun x => x < length l) fool));
    clear l; intros.
  + apply H; constructor.
  + apply H0.
  + apply H. lia. constructor. lia. apply H1.
Qed.

Equations? interval x y : list nat by rec (y - x) lt :=
  interval x y with lt_dec x y :=
    { | left  ltxy  => x :: interval (S x) y;
      | right nltxy => [] }.
Proof. lia. Defined.

Lemma interval_empty x : interval x x = [].
Proof. funelim (interval x x). clear Heq; now apply Nat.lt_irrefl in l. reflexivity. Qed.

Lemma interval_large x y : ~ x < y -> interval x y = [].
Proof. funelim (interval x y); clear Heq; intros; now try lia. Qed.

Lemma foo_spec2 l : foo l = interval 0 (length l).
Proof.
  set (P := fun start (l fool : list nat) => fool = interval start (length l)).
  revert l.
  apply (foo_elim (P 0)
          (fun l acc n fool =>
             n <= length l ->
             acc = interval n (length l) ->
             fool = interval 0 (length l))); subst P; simpl.
  intros l.
  + intros H. apply H; auto. rewrite interval_large; trivial; lia.
  + intros; trivial.
  + intros l ? n H Hn ->. apply H. lia.
    rewrite (interval_equation_1 n).
    destruct lt_dec. reflexivity. elim n0. lia.
Qed.
