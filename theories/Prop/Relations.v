(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Corelib Require Import Relation_Definitions.
From Corelib Require Import Init.Wf.
From Corelib Require Export Program.Wf.

(** Explicitely transparent proofs of well-foundedness of transitive closures and 
  standard ordering on natural numbers. *)

Inductive clos_trans {A} {R : relation A} (x : A) : A -> Prop :=
| t_step (y:A) : R x y -> clos_trans x y
| t_trans (y z:A) : clos_trans x y -> clos_trans y z -> clos_trans x z.

Arguments clos_trans A R x y : clear implicits.

#[export]
Hint Resolve t_step : relations.

Lemma wf_clos_trans {A R} : well_founded R -> well_founded (clos_trans A R).
Proof.
  intros wf x.
  specialize (wf x).
  induction wf as [x _ Hcl].
  constructor. intros y cl.
  induction cl as [y x hxy|]. eapply Hcl, hxy. 
  apply IHcl2. apply Hcl. apply cl1.
Defined.

Implicit Types m n p : nat.

Section Well_founded_Nat.

Variable A : Type.

Variable f : A -> nat.
Definition ltof (a b:A) := f a < f b.
Definition gtof (a b:A) := f b > f a.

Lemma lt_le_trans x y z : x < y -> y <= z -> x < z.
Proof. 
  induction 2; auto.
Qed.

Lemma succ_le_mono n m : S n <= S m -> n <= m.
Proof.
  change n with (pred (S n)) at 2.
  change m with (pred (S m)) at 2.
  induction 1; cbn in *. constructor. destruct m0; auto.
Qed. 
  
Theorem well_founded_ltof : well_founded ltof.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc ltof a).
  { intro n; induction n as [|n IHn].
    - intros a Ha; absurd (f a < 0); auto. inversion Ha.
    - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
      apply IHn. apply lt_le_trans with (f a); auto. now apply succ_le_mono. }
  intros a. apply (H (S (f a))). constructor.
Defined.
End Well_founded_Nat.

Lemma lt_wf : well_founded lt.
Proof.
  exact (well_founded_ltof nat (fun x => x)).
Defined.