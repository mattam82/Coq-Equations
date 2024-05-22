(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** An example development of the [fin] datatype using [equations]. *)

Require Import Program.Basics Program.Combinators.
From Equations Require Import Equations.
Open Scope equations_scope.
(** [fin n] is the type of naturals smaller than [n]. *)

Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature for fin.
(** NoConfusion For [fin]. *)
Derive NoConfusion NoConfusionHom for fin.

(** We can inject it into [nat]. *)
Equations fog {n} (f : fin n) : nat :=
fog (n:=?(S n)) (@fz n) := 0 ;
fog (fs f) := S (fog f).

(** The injection preserves the number: *)
Lemma fog_inj {n} (f : fin n) : fog f < n.
Proof with auto with arith. intros.
  depind f; simp fog...
Qed.

(** Of course it has an inverse. *)

Equations gof n : fin (S n) :=
gof O := fz ;
gof (S n) := fs (gof n).

Lemma fog_gof n : fog (gof n) = n.
Proof with auto with arith.
  intros. funelim (gof n)... simp fog; congruence.
Qed.

Equations fin_inj_one {n} (f : fin n) : fin (S n) :=
fin_inj_one fz := fz;
fin_inj_one (fs f) := fs (fin_inj_one f).

Inductive le : nat -> nat -> Type :=
| le_O n : 0 <= n
| le_S {n m} : n <= m -> S n <= S m
where "n <= m" := (le n m).
Derive Signature for le.

Equations le_S_inv {n m} (p : S n <= S m) : n <= m :=
le_S_inv (le_S p) := p.

Equations fin_inj {n} {m} (f : fin n) (k : n <= m) : fin m :=
fin_inj fz (le_S p) := fz;
fin_inj (fs f) (le_S p) := fs (fin_inj f p).

(** Let's do some arithmetic on [fin] *)

(* Equations fin_plus {n m} (x : fin n) (y : fin m) : fin (n + m) := *)
(* fin_plus (fz n) f := fin_inj f _ ; *)
(* fin_plus (fs n x) y := fs (fin_plus x y). *)
(* Next Obligation. destruct n; try constructor. *)
(** Won't pass the guardness check which diverges anyway. *)

Inductive finle : forall (n : nat) (x : fin n) (y : fin n), Prop :=
| leqz : forall {n j}, finle (S n) fz j
| leqs : forall {n i j}, finle n i j -> finle (S n) (fs i) (fs j).

Scheme finle_ind_dep := Induction for finle Sort Prop.

#[export] Instance finle_ind_pack n x y : DepElim.DependentEliminationPackage (finle n x y) :=
  { elim_type := _ ; elim := finle_ind_dep }.

Arguments finle {n}.

Require Vectors.Vector.
Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

Equations nth {A} {n} (v : Vector.t A n) (f : fin n) : A :=
nth (vcons a v) fz := a ;
nth (vcons a v) (fs f) := nth v f.

Equations tabulate {A} {n} (f : fin n -> A) : Vector.t A n by struct n :=
tabulate (n:=O) f := vnil ;
tabulate (n:=(S n)) f := vcons (f fz) (tabulate (f ∘ fs)).

(** [Below] recursor for [fin]. *)

Equations Below_fin (P : forall n, fin n -> Type) {n} (v : fin n) : Type :=
Below_fin P fz := unit ;
Below_fin P (fs f) := (P _ f * Below_fin P f)%type.

#[export] Hint Rewrite Below_fin_equation_2 (* Below_fin_equation_3 *) : rec_decision.

Equations(noeqns noind) below_fin (P : forall n, fin n -> Type)
  (step : forall n (v : fin n), Below_fin P v -> P n v)
  {n} (v : fin n) : Below_fin P v :=
below_fin P step fz := tt ;
below_fin P step (@fs n f) :=
  let bf := below_fin P step f in
    (step n f bf, bf).

Global Opaque Below_fin.

Definition rec_fin (P : forall n, fin n -> Type) {n} v
  (step : forall n (v : fin n), Below_fin P v -> P n v) : P n v :=
  step n v (below_fin P step v).

(* Import Equations.Below. *)

(* Instance fin_Recursor n : Recursor (fin n) := *)
(*   { rec_type := fun v => forall (P : forall n, fin n -> Type) step, P n v; *)
(*     rec := fun v P step => rec_fin P v step }. *)
