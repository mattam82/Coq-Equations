(** Example by Nicky Vazou, unfinished *)

Require Import Arith.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Program.Wf.
Require Import List.
Require Import PeanoNat.
Require Import Program.
Require Import Wf.
Require Import Equations.

Import ListNotations.

Class Associative {T: Type} (op: T -> T -> T) :=
  {
    associativity: forall x y z, op x (op y z) = op (op x y) z;
  }.

Class Monoid (T: Type) :=
  MkMonoid {
    unit: T;
    op: T -> T -> T;
    monoid_associative: Associative op;
    monoid_left_identity: forall x, op unit x = x;
    monoid_right_identity: forall x, op x unit = x;
  }.

Instance app_Associative: forall T, Associative (@app T).
Proof.
  intro T.
  constructor.
  induction x.
  { reflexivity. }
  { simpl. congruence. }
Defined.

Instance list_Monoid: forall T, Monoid (list T).
Proof.
  intro T.
  apply MkMonoid with (unit := []) (op := @app T).
  { auto with typeclass_instances. }
  { reflexivity. }
  { induction x.
    { reflexivity. }
    { simpl. congruence. }
  }
Defined.

Notation "a ** b" := (op a b) (at level 50).

Class MonoidMorphism
      {Tn Tm: Type}
      `{Mn: Monoid Tn} `{Mm: Monoid Tm}
      (f: Tn -> Tm)
  :=
  {
    morphism_unit: f unit = unit;
    morphism_op: forall x y, f (x ** y) = f x ** f y;
  }.

Class ChunkableMonoid (T: Type) `{Monoid T} :=
  MkChunkableMonoid {
    length: T -> nat;
    drop: nat -> T -> T;
    take: nat -> T -> T;
    drop_spec:
      forall i x,
        i <= length x ->
        length (drop i x) = length x - i;
    take_spec:
      forall i x,
        i <= length x ->
        length (take i x) = i;
    take_drop_spec:
      forall i x, x = take i x ** drop i x;
  }.

Fixpoint list_take {T: Type} i (l: list T) :=
  match i, l with
  | 0, _ => []
  | _, [] => []
  | S i, h::t => h :: list_take i t
  end.

Fixpoint list_drop {T: Type} i (l: list T) :=
  match i, l with
  | 0, _ => l
  | _, [] => []
  | S i, h::t => list_drop i t
  end.

Instance list_ChunkableMonoid: forall T, ChunkableMonoid (list T).
Proof.
  intro T.
  apply MkChunkableMonoid
  with (length := @List.length T) (drop := list_drop) (take := list_take);
    intros.
  { generalize dependent x.
    induction i, x; intros; intuition.
  }
  { generalize dependent x.
    induction i, x; intros; intuition.
    simpl in *.
    rewrite IHi; intuition.
  }
  { generalize dependent x.
    induction i, x; intros; intuition.
    simpl in *.
    rewrite <- IHi.
    reflexivity.
  }
Defined.
Require Import Omega.
Section Chunk.
  Context{T : Type} `{M : ChunkableMonoid T}.
  Set Program Mode.
  Equations chunk (i: { i: nat | i > 0 }) (x: T) : list T by rec (length x) lt :=
  chunk i x with dec (Nat.leb (length x) i) :=    
    { | left _ => [x] ;
      | right p => take i x :: chunk i (drop i x) }.
  Next Obligation.
    red.
    apply leb_complete_conv in p.
    rewrite drop_spec. omega. auto with arith.
  Defined.
End Chunk.

(** Bugs, rewrite hint db is not discharged *)
Hint Rewrite @chunk_helper_1_equation_2 @chunk_helper_1_equation_1 @chunk_equation_1 : chunk.

Theorem if_flip_helper {B: Type} {b: bool}
        (C E: true = b -> B) (D F: false = b -> B):
  (forall (r: true  = b), C r = E r) ->
  (forall (r: false = b), D r = F r) ->
  (if b as an return an = b -> B then C else D) eq_refl =
  (if b as an return an = b -> B then E else F) eq_refl.
Proof.
  intros.
  destruct b.
  apply H.
  apply H0.
Qed.

Eval compute in (chunk (exist _ 3 _) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]).
(*
  = [[0; 1; 2]; [3; 4; 5]; [6; 7; 8]; [9]]
  : list (list nat)
 *)

Section mconcat.
  Context {M : Type} `{Monoid M}.

  Equations mconcat (l: list M): M :=
  mconcat [] := unit;
  mconcat (cons x xs) := x ** mconcat xs.
End mconcat.
Transparent mconcat.

Definition strong_induction := well_founded_induction lt_wf.

Derive NoConfusion for N.

Theorem morphism_distribution:
  forall {M N: Type}
    `{MM: Monoid M} `{MN: Monoid N}
    `{CMM: @ChunkableMonoid N MN}
    (f: N -> M)
    `{MMf: @MonoidMorphism _ _ MN MM f},
    forall i x,
      f x = mconcat (map f (chunk i x)).
Proof.
  intros.
  funelim (chunk i x).
  { simpl. simp mconcat. now rewrite monoid_right_identity. }
  simpl. simp mconcat.
  rewrite <- H; auto.
  rewrite <- morphism_op.
  now rewrite <- take_drop_spec.
Qed.

Lemma length_list_drop: forall {T: Type} i (x: list T),
  i < Datatypes.length x ->
  Datatypes.length (list_drop i x) = Datatypes.length x - i.
Proof.
  intros.
  generalize dependent i.
  induction x; destruct i; simpl; intros.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { apply IHx. intuition. }
Qed.

Lemma length_chunk_base:
  forall {T: Type} I (x: list T),
    let i := proj1_sig I in
    i > 1 ->
    Datatypes.length x <= i ->
    Datatypes.length (chunk I x) = 1.
Proof.
  intros; subst i.
  funelim (chunk I x). reflexivity.
  simpl. 
  apply leb_correct in H1. rewrite e0 in H1. discriminate.
Qed.
Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

Lemma length_chunk_lt:
  forall {T: Type} I (x: list T),
    let i := proj1_sig I in
    i > 1 ->
    Datatypes.length x > i ->
    Datatypes.length (chunk I x) < Datatypes.length x.
Proof.
  intros; subst i.
  funelim (chunk I x).
  simpl. omega.
  simpl.
  specialize (H H0).
  revert H. unfold drop. simpl.
  pose proof (drop_spec (` I) x). simpl in H.
  rewrite H by omega. clear H.
  simp chunk. clear Heq. destruct dec. simp chunk; simpl; intros; try omega. intros.
  feed H. 
  clear H. apply leb_complete_conv in e. 
  pose proof (drop_spec (` I) x). rewrite H in e; try omega;
                                    unfold length in *; simpl in *; omega.
  omega.
Qed.

Section pmconcat.
  Context {M : Type} `{ChunkableMonoid M}.

  Equations pmconcat (I : { i : nat | i > 0 }) (x : list M) : M by rec (length x) lt :=
  pmconcat i x with dec ((` i <=? 1) || (length x <=? ` i))%bool => {
    | left H => mconcat x ;
    | right Hd => pmconcat i (map mconcat (chunk i x)) }.

  Next Obligation.
    red. clear pmconcat.
    rewrite map_length.
    rewrite Bool.orb_false_iff in Hd.
    destruct Hd. apply leb_complete_conv in H2. apply leb_complete_conv in H3.
    apply length_chunk_lt; simpl; auto.
  Time Qed. (* 0.264s from 1.571s *)
End pmconcat.

Instance mconcat_mon T : MonoidMorphism (@mconcat (list T) _).

Next Obligation.
Proof.
  funelim (mconcat x). reflexivity.
  simpl. rewrite H. now rewrite <- app_assoc.
Qed.

Theorem concatEquivalence: forall {T: Type} i (x: list (list T)),
    pmconcat i x = mconcat x.
Proof.
  intros.
  funelim (pmconcat i x).
  reflexivity.
  rewrite H. now rewrite <- (morphism_distribution mconcat). 
Qed.
