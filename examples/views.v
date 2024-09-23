(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(* end hide *)

From Equations Require Import Equations.
From Stdlib Require Import List Program.Syntax Arith Lia.

(** * Views using dependent pattern-matching

  The standard notion of pattern-matching in type theory requires to
  give a case for each constructor of the inductive type we are working
  on, even if the function acts the same on a subset of distinct
  constructors. The reason is that due to dependencies, it is not clear
  that two branches for distinct constructors can be factorized in general:
  the return types of branches could be unifiable or not, depending on the
  branch body.

  Rather than trying to internalise this notion in the pattern-matching
  algorithm we propose the use of views to encode this phenomenon.

  Suppose that we want to do case analysis on an inductive with
  three constructors but only want to single out the [cone] constructor during
  pattern-matching: *)

Inductive three := cone | ctwo | cthree.

(** The user can write a view function to implement this. First one needs to write
    a discriminator for the inductive type, indicating which cases are to be merged together:
 *)
Equations discr_three (c : three) : Prop :=
  discr_three cone := False;
  discr_three _ := True.

(** One can derive an inductive representing the view of [three] as [cone] and the two other
    [ctwo] and [cthree] cases lumbed together. *)
Inductive three_two_view : three -> Set :=
| three_one : three_two_view cone
| three_other c : discr_three c -> three_two_view c.

(** This view is obviously inhabited for any element in [three]. *)
Equations three_viewc c : three_two_view c :=
three_viewc cone := three_one;
three_viewc c := three_other c I.

(** Using a [with] clause one can pattern-match on the view argument to
    do case splitting on [three] using only two cases. In each branch,
    one can see that the [three] variable is determined by the view pattern.  *)
Equations onthree (c : three) : three :=
  onthree c with three_viewc c :=
  onthree ?(cone) three_one := cone;
  onthree ?(c) (three_other c Hc) := c.

(** A similar example discriminating [10] from the rest of natural numbers. *)

Equations discr_10 (x : nat) : Prop :=
  discr_10 10 := False;
  discr_10 x := True.

(** First alternative: using an inductive view *)

Module View.
Inductive view_discr_10 : nat -> Set :=
| view_discr_10_10 : view_discr_10 10
| view_discr_10_other c : discr_10 c -> view_discr_10 c.

(** This view is obviously inhabited for any element in [three]. *)
Equations discr_10_view c : view_discr_10 c :=
discr_10_view 10 := view_discr_10_10;
discr_10_view c := view_discr_10_other c I.

Equations f (n:nat) : nat :=
f n with discr_10_view n :=
f ?(10) view_discr_10_10 := 0;
f ?(n) (view_discr_10_other n Hn) := n + 1.

Goal forall n, n <> 10 -> f n = n + 1.
  intros n; apply f_elim.
 (* 2 cases: 10 and not 10 *)
  all:simpl; congruence.
Qed.
End View.

(** Second alternative: using the discriminator directly.
    This currently requires massaging the eliminator a bit *)

Equations f (n:nat) : nat by struct n (* FIXME *) :=
{ f 10 := 0;
  f x  := brx x (I : discr_10 x) }
where brx (x : nat) (H : discr_10 x) : nat :=
      brx x H := x + 1.

Lemma f_elim' : forall (P : nat -> nat -> Prop),
    P 10 0 ->
    (forall (x : nat) (H : discr_10 x), P x (x + 1)) ->
    (forall n : nat, P n (f n)).
Proof.
  intros. apply (f_elim P (fun x H r => P x r)); auto.
Defined.

Goal forall n, n <> 10 -> f n = n + 1.
  intros n; apply f_elim'.
 (* 2 cases: 10 and not 10 *)
  all:simpl; congruence.
Qed.