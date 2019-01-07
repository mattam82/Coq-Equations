From Equations Require Import Equations.

Require Import List Program.Syntax Arith Lia.

Equations foo : list nat -> list nat :=
  foo l := go [] (length l)

  where go : list nat -> nat -> list nat :=
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

Section Fast_length.
  Context {A : Type}.

  Equations fast_length (l : list A) : nat :=
  fast_length l := go 0 l

    where go : nat -> list A -> nat :=
          go n [] := n;
          go n (_ :: l) := go (S n) l.
End Fast_length.

Lemma fast_length_length : forall {A} (l : list A), length l = fast_length l.
Proof.
  intros A.
  apply (fast_length_elim (fun l n => length l = n)
                          (fun l n l' lenl =>
                             length l = n + length l' ->
                             length l = lenl));
    intros l H; simpl in *; intuition auto with arith; lia.
Qed.

Equations list_init {A} (n : nat) (a : A) : list A :=
  list_init 0 _ := [];
  list_init (S n) x := x :: list_init n x.

Require Import NArith.

Equations pos_list_init {A} (n : positive) (a : A) : list A :=
  pos_list_init xH x := [x];
  pos_list_init (n~1) x := let l := pos_list_init n x in x :: l ++ l;
  pos_list_init (n~0) x := let l := pos_list_init n x in x :: l ++ l.
(* Time Definition big_interval := Eval vm_compute in pos_list_init 20000 true. *)

(* Extraction length. *)
(* Extraction fast_length. *)

(* Time Definition slow := Eval vm_compute in length big_interval. *)
(* Time Definition fast := Eval vm_compute in fast_length big_interval. *)

Hint Extern 100 => progress (simpl in *) : Below.

Equations? isPrime (n : nat) : bool :=
  isPrime 0 := false;
  isPrime 1 := false;
  isPrime 2 := true;
  isPrime 3 := true;
  isPrime k := worker 2
    where worker (n' : nat) : bool by rec (k - n') lt :=
    worker i with ge_dec i k :=
      { | left H := true;
        | right H with eq_nat_dec (Nat.modulo k i) 0 :=
            { worker i (right H) (left H') := false;
              worker i (right H) (right H') := worker (S i) } }.
Proof. clear worker. subst k. do 4 (destruct i; try lia). Defined.
