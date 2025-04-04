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

Inductive clos_trans {A} {R : relation A} (x : A) : A -> Prop :=
| t_step (y:A) : R x y -> clos_trans x y
| t_trans (y z:A) : clos_trans x y -> clos_trans y z -> clos_trans x z.

Arguments clos_trans A R x y : clear implicits.

Lemma wf_clos_trans {A R} : well_founded R -> well_founded (clos_trans A R).
Proof.
  intros wf x.
  specialize (wf x).
  induction wf as [x _ Hcl].
  constructor. intros y cl.
  induction cl as [y x hxy|]. eapply Hcl, hxy. 
  apply IHcl2. apply Hcl. apply cl1.
Defined.

Lemma lt_wf : well_founded lt.
Proof.
  intros x; induction x as [|x' IH].
  - constructor; intros y lt; inversion lt.
  - constructor; intros y lt. inversion_clear lt; auto.
    now apply Acc_inv with x'.
Defined.