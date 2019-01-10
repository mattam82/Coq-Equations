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
        | right H := if Nat.eqb (Nat.modulo k i) 0 then false else worker (S i) }.
Proof. subst k. do 4 (destruct i; try lia). Defined.

Require Import ExtrOcamlBasic.

Extraction isPrime.

(* Definition isPrime_unfold' n := *)
(*   match n with *)
(*   | 0 | 1 => false *)
(*   | 2 | 3 => true *)
(*   | S (S (S (S k))) => isPrime_unfold_clause_5_worker k 2 *)
(*   end. *)

(* Lemma isPrime_unfold'_eq n : isPrime n = isPrime_unfold' n. *)
(* Proof. *)
(*   revert n. *)
(*   apply (isPrime_elim (fun n b => b = isPrime_unfold' n) (fun n n' b => b = isPrime_unfold_clause_5_worker n n')); *)
(*     simpl; try reflexivity. *)
(*   intros. *)
(*   unfold isPrime_unfold_clause_5_worker. rewrite Heq. simpl. reflexivity. *)
(*   intros. *)
(*   unfold isPrime_unfold_clause_5_worker. rewrite Heq. simpl. *)
(*   rewrite isPrime_clause_5_worker_unfold_eq. reflexivity. *)
(* Defined. *)

Equations rev_acc {A} (l : list A) : list A :=
  rev_acc l := go [] l

   where go : list A -> list A -> list A :=
         go acc [] := acc;
         go acc (hd :: tl) := go (hd :: acc) tl.

Lemma rev_acc_eq : forall {A} (l : list A), rev_acc l = rev l.
Proof.
  apply (rev_acc_elim (fun A l r => r = rev l)
                      (fun A _ acc l r => r = rev l ++ acc)); intros; simpl.
  + now rewrite app_nil_r in H.
  + reflexivity.
  + now rewrite H, <- app_assoc.
Qed.

Equations nat4_discr : nat -> Set :=
nat4_discr 0 := False;
nat4_discr 1 := False;
nat4_discr 2 := False;
nat4_discr n := True.

Inductive nat4_inv : nat -> Set :=
| nat4_inv_0 : nat4_inv 0
| nat4_inv_1 : nat4_inv 1
| nat4_inv_2 : nat4_inv 2
| nat4_inv_n n : nat4_discr n -> nat4_inv n.

Equations nat4_view (n : nat) : nat4_inv n :=
| 0 => nat4_inv_0;
| 1 => nat4_inv_1;
| 2 => nat4_inv_2;
| n => nat4_inv_n n I.

Obligation Tactic := idtac.

Equations? nat4 (n : nat) : nat by rec n lt :=
nat4 n with nat4_view n :=
  { nat4 ?(0) nat4_inv_0 := 0;
    | nat4_inv_1 := 1;
    | nat4_inv_2 := 1;
    | nat4_inv_n k Hn := nat4 (pred k) }.
Proof. destruct k. destruct Hn. auto with arith. Defined.

Inductive three := cone | ctwo | cthree.

Equations discr_three (c : three) : Prop :=
  discr_three cone := False;
  discr_three _ := True.

Inductive three_view : three -> Set :=
| three_one : three_view cone
| three_other c : discr_three c -> three_view c.
Equations three_viewc c : three_view c :=
three_viewc cone := three_one;
three_viewc c := three_other c I.

Equations onthree (c : three) : three :=
  onthree c with three_viewc c :=
  onthree ?(cone) three_one := cone;
  onthree ?(c) (three_other c Hc) := c.
Require Import List.

Equations filter_length {A} (l : list A) (f : A -> bool) : length (filter f l) <= length l :=
 filter_length [] f := le_n 0;
 filter_length (x :: xs) f with f x :=
                         { | true => le_n_S _ _ (filter_length xs f);
                           | false => le_S _ _ (filter_length xs f) }.

Section nubBy.
  Context {A} (eq : A -> A -> bool).

  Equations? nubBy (l : list A) : list A by rec (length l) lt :=
  nubBy []        => [];
  nubBy (x :: xs) => x :: nubBy (filter (fun y => negb (eq x y)) xs).
  Proof. simpl. auto using filter_length with arith. Defined.
End nubBy.

Lemma nubBy_length {A} (eq : A -> A -> bool) (l : list A) : length (nubBy eq l) <= length l.
Proof.
  funelim (nubBy eq l); simpl; trivial.
  rewrite (filter_length l) in H. auto with arith.
Qed.

Lemma In_filter {A} (f : A -> bool) (l : list A) a : In a (filter f l) -> In a l /\ f a = true.
Proof.
  induction l; simpl. intros [].
  destruct (f a0) eqn:Heq.
  simpl. intuition auto. now subst a0.
  intuition auto.
Qed.

Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A) :
  In a (nubBy eq l) -> In a l.
Proof.
  funelim (nubBy eq l).
  + trivial.
  + rename a0 into b. intros H0.
    destruct H0 as [->|H0]; auto. simpl. auto.
    specialize (H _ H0). apply In_filter in H as [Inal eqa]. right; auto.
Qed.

Lemma nuBy_nodup {A} (eq : A -> A -> bool) (l : list A) :
  (forall x y, (eq x y = true) <-> (x = y)) -> NoDup (nubBy eq l).
Proof.
  funelim (nubBy eq l). constructor. intros Heq; specialize (H Heq).
  constructor. intros Hi. apply In_nubBy, In_filter in Hi as [_ eqaa].
  specialize (Heq a a). destruct (eq a a). discriminate.
  destruct (proj2 Heq). reflexivity. discriminate.
  auto.
Qed.