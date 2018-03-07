(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** An example development of the [fin] datatype using [equations]. *)

Require Import HoTT.Basics.Overture.
Require Import HoTT.Spaces.Nat.
Require Import HoTT.DProp.
Require Import Equations.Equations.

(** [fin n] is the type of naturals smaller than [n]. *)

Inductive fin : nat -> Set :=
| fz : forall {n : nat}, fin (S n)
| fs : forall {n : nat}, fin n -> fin (S n).

(** We can inject it into [nat]. *)

Equations(nocomp) fog {n} (f : fin n) : nat :=
fog {n:=?(S n)} (fz n) := 0 ; 
fog (fs n f) := S (fog f).

(** The injection preserves the number: *)
Require Import FunctionalInduction.

Lemma fog_inj {n} (f : fin n) : fog f < n.
Proof. intros.
  depind f; simp fog; constructor.
Qed.

(** Of course it has an inverse. *)

Equations(nocomp) gof n : fin (S n) :=
gof O := fz ;
gof (S n) := fs (gof n).

Lemma fog_gof n : fog (gof n) = n.
Proof with auto.  (* funind (gof n) gofn; simp fog gof... *)
  induction n; simp fog gof; rewrite IHn...
Qed.

(** Let's do some arithmetic on [fin] *)

(* Equations_nocomp fin_plus {n m} (x : fin n) (y : fin m) : fin (n + m) := *)
(* fin_plus ?(S n) ?(S m) (fz n) (fz m) := fz ; *)
(* fin_plus ?(S n) ?(S m) (fs n x) y := fs (fin_plus x y) ; *)
(* fin_plus ?(S n) ?(S m) (fz n) (fs m y) := fs (fin_plus fz y).  *)

(** Won't pass the guardness check which diverges anyway. *)

Inductive finle : forall (n : nat) (x : fin n) (y : fin n), Type :=
| leqz : forall {n j}, finle (S n) fz j
| leqs : forall {n i j}, finle n i j -> finle (S n) (fs i) (fs j).

Scheme finle_ind_dep := Induction for finle Sort Type.

Instance finle_ind_pack n x y : DependentEliminationPackage (finle n x y) :=
  { elim_type := _ ; elim := finle_ind_dep }.

Arguments finle {n}.

(* FIXME Missing Vector.

Require Vectors.Vector.
Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

Equations(nocomp) nth {A} {n} (v : Vector.t A n) (f : fin n) : A :=
nth (vcons a _ v) fz := a ;
nth (vcons a _ v) (fs n f) := nth v f.

Equations(nocomp) tabulate {A} {n} (f : fin n -> A) : Vector.t A n :=
tabulate {n:=O} f := vnil ;
tabulate {n:=(S n)} f := vcons (f fz) (tabulate (f ∘ fs)).

(** NoConfusion For [fin]. *)

Derive NoConfusion for fin.

(** [Below] recursor for [fin]. *)

Equations(nocomp noind) Below_fin (P : forall n, fin n -> Type) {n} (v : fin n) : Type :=
Below_fin P fz := unit ;
Below_fin P (fs n f) := (P n f * Below_fin P f)%type.

Hint Rewrite Below_fin_equation_2 (* Below_fin_equation_3 *) : Below.

Equations(nocomp noeqns noind) below_fin (P : forall n, fin n -> Type)
  (step : forall n (v : fin n), Below_fin P v -> P n v)
  {n} (v : fin n) : Below_fin P v :=
below_fin P step fz := tt ;
below_fin P step (fs n f) := 
  let bf := below_fin P step f in
    (step n f bf, bf).

Global Opaque Below_fin.

Definition rec_fin (P : forall n, fin n -> Type) {n} v
  (step : forall n (v : fin n), Below_fin P v -> P n v) : P n v :=
  step n v (below_fin P step v).

Import Equations.Below.

Instance fin_Recursor n : Recursor (fin n) :=
  { rec_type := fun v => forall (P : forall n, fin n -> Type) step, P n v;
    rec := fun v P step => rec_fin P v step }.

*)
