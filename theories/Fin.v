(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** An example development of the [fin] datatype using [equations]. *)

Require Import Coq.Program.Program Equations.Equations.

(** [fin n] is the type of naturals smaller than [n]. *)

Inductive fin : nat -> Set :=
| fz : ∀ {n}, fin (S n)
| fs : ∀ {n}, fin n -> fin (S n).

(** We can inject it into [nat]. *)

Equations(nocomp) fog {n} (f : fin n) : nat :=
fog ?(S n) (fz n) := 0 ; 
fog ?(S n) (fs n f) := S (fog f).

(** The injection preserves the number: *)

Lemma fog_inj {n} (f : fin n) : fog f < n.
Proof with auto with arith. intros.
  depind f; simp fog...
Qed.

(** Of course it has an inverse. *)

Equations(nocomp) gof n : fin (S n) :=
gof O := fz ;
gof (S n) := fs (gof n).

Lemma fog_gof n : fog (gof n) = n.
Proof with auto with arith. intros.
  funind (gof n) gofn; simp fog gof...
Qed.

(** Let's do some arithmetic on [fin] *)

(* Equations_nocomp fin_plus {n m} (x : fin n) (y : fin m) : fin (n + m) := *)
(* fin_plus ?(S n) ?(S m) (fz n) (fz m) := fz ; *)
(* fin_plus ?(S n) ?(S m) (fs n x) y := fs (fin_plus x y) ; *)
(* fin_plus ?(S n) ?(S m) (fz n) (fs m y) := fs (fin_plus fz y).  *)


(** Won't pass the guardness check which diverges anyway. *)

Inductive finle : ∀ (n : nat) (x : fin n) (y : fin n), Prop :=
| leqz : ∀ {n j}, finle (S n) fz j
| leqs : ∀ {n i j}, finle n i j -> finle (S n) (fs i) (fs j).

Scheme finle_ind_dep := Induction for finle Sort Prop.

Instance finle_ind_pack n x y : DependentEliminationPackage (finle n x y) :=
  { elim_type := _ ; elim := finle_ind_dep }.

Implicit Arguments finle [[n]].

(* Equations trans {n} {i j k : fin n} (p : finle i j) (q : finle j k) : finle i k := *)
(* trans ?(S _) ?(fz) ?(j) ?(k) leqz q := leqz ; *)
(* trans ?(S n) ?(fs i) ?(fs j) ?(fs k) (leqs p) (leqs q) := leqs (trans p q). *)

(* Lemma trans_eq1 n (j k : fin (S n)) (q : finle j k) : trans leqz q = leqz. *)
(* Proof. intros. simplify_equations ; reflexivity. Qed. *)

(* Lemma trans_eq2 n i j k p q : @trans (S n) (fs i) (fs j) (fs k) (leqs p) (leqs q) = leqs (trans p q). *)
(* Proof. intros. simplify_equations ; reflexivity. Qed. *)

Require Import Bvector.

Equations(nocomp) nth {A} {n} (v : vector A n) (f : fin n) : A :=
nth A ?(S n) (Vcons a n v) fz := a ;
nth A ?(S n) (Vcons a n v) (fs n f) := nth v f.

Goal ∀ (A : Type) (n : nat) (a : A) (H : vector A n), nth (Vcons a H) fz = a.
  intros. funind (nth (Vcons a H) fz) nfz.
Qed.

Equations(nocomp) tabulate {A} {n} (f : fin n -> A) : vector A n :=
tabulate A O f := Vnil ;
tabulate A (S n) f := Vcons (f fz) (tabulate (f ∘ fs)).

(** NoConfusion For [fin]. *)

Derive NoConfusion for fin.

(* Equations (nocomp noeqns noind) NoConfusion_fin {n : nat} (P : Type) (x y : fin n) : Type := *)
(* NoConfusion_fin (S n) P (fz n) (fz n) := P -> P ; *)
(* NoConfusion_fin (S n) P (fz n) (fs n y) := P ; *)
(* NoConfusion_fin (S n) P (fs n x) (fz n) := P ; *)
(* NoConfusion_fin (S n) P (fs n x) (fs n y) := (x = y -> P) -> P. *)

(* Transparent NoConfusion_fin. *)

(* Equations (nocomp noind) noConfusion_fin {n} P (x y : fin n) (H : x = y) : NoConfusion_fin P x y := *)
(* noConfusion_fin (S n) P (fz n) (fz n) eq_refl := λ p, p ; *)
(* noConfusion_fin (S n) P (fs ?(n) x) (fs ?(n) x) eq_refl := λ p : x = x -> P, p eq_refl. *)

(* Global Opaque noConfusion_fin. *)
(* Hint Rewrite @noConfusion_fin_equation_2 @noConfusion_fin_equation_5 : equations. *)
(* Hint Immediate @noConfusion_fin_equation_1 @noConfusion_fin_equation_3 @noConfusion_fin_equation_4 : equations. *)

(* Instance fin_noconf n : NoConfusionPackage (fin n) := *)
(*   { NoConfusion := NoConfusion_fin ; *)
(*     noConfusion := noConfusion_fin }. *)

(** [Below] recursor for [fin]. *)

Equations(nocomp noind) Below_fin (P : ∀ n, fin n -> Type) {n} (v : fin n) : Type :=
Below_fin P (S n) fz := unit ;
Below_fin P (S n) (fs n f) := (P n f * Below_fin P f)%type.

Hint Rewrite Below_fin_equation_2 Below_fin_equation_3 : Below.

Equations(nocomp noeqns noind) below_fin (P : ∀ n, fin n -> Type)
  (step : ∀ n (v : fin n), Below_fin P v -> P n v)
  {n} (v : fin n) : Below_fin P v :=
below_fin P step (S n) fz := tt ;
below_fin P step (S n) (fs n f) := 
  let bf := below_fin P step f in
    (step n f bf, bf).

Global Opaque Below_fin.

Definition rec_fin (P : ∀ n, fin n -> Type) {n} v
  (step : ∀ n (v : fin n), Below_fin P v -> P n v) : P n v :=
  step n v (below_fin P step v).

Instance fin_Recursor n : Recursor (fin n) :=
  { rec_type := λ v, ∀ (P : ∀ n, fin n -> Type) step, P n v;
    rec := λ v P step, rec_fin P v step }.
