From Equations Require Import Init DepElim FunctionalInduction Classes.

(** Naturals *)
Register Init.Datatypes.O as equations.nat.zero.
Register Init.Datatypes.S as equations.nat.succ.
Register Init.Datatypes.nat as equations.nat.type.

(** Heterogeneous equality *)
Register Logic.JMeq.JMeq as equations.JMeq.type.
Register Logic.JMeq.JMeq_refl as equations.JMeq.refl.

Register Equations.Init.sigma as equations.sigma.type.
Register Equations.Init.sigmaI as equations.sigma.intro.
Register Equations.Init.pr1 as equations.sigma.pr1.
Register Equations.Init.pr2 as equations.sigma.pr2.

Register Equations.Init.sigmaP as equations.sigmaP.type.
Register Equations.Init.sigmaPI as equations.sigmaP.intro.
Register Equations.Init.prP1 as equations.sigmaP.pr1.
Register Equations.Init.prP2 as equations.sigmaP.pr2.

Register Equations.Init.sigmaSP as equations.sigmaSP.type.
Register Equations.Init.sigmaSPI as equations.sigmaSP.intro.
Register Equations.Init.prSP1 as equations.sigmaSP.pr1.
Register Equations.Init.prSP2 as equations.sigmaSP.pr2.

(** Classes *)
Register Equations.FunctionalInduction.FunctionalInduction as equations.funind.class.
Register Equations.FunctionalInduction.FunctionalElimination as equations.funelim.class.
Register Equations.DepElim.DependentEliminationPackage as equations.depelim.class.
Register Equations.DepElim.ImpossibleCall as equations.impossiblecall.class.

Register Equations.Signature.Signature as equations.signature.class.
Register Equations.Signature.signature as equations.signature.signature.
Register Equations.Signature.signature_pack as equations.signature.pack.

(** Internally used constants *)

Register Equations.Init.fixproto as equations.fixproto.
Register Equations.Init.hidebody as equations.internal.hidebody.
Register Equations.DepElim.inaccessible_pattern as equations.internal.inaccessible_pattern.
Register Equations.DepElim.block as equations.internal.block.
Register Equations.DepElim.hide_pattern as equations.internal.hide_pattern.
Register Equations.DepElim.add_pattern as equations.internal.add_pattern.
Register Equations.DepElim.the_end_of_the_section as equations.internal.the_end_of_the_section.
Register Equations.DepElim.end_of_section as equations.internal.end_of_section.

(** Logic parameterization *)
Inductive sBox (A : SProp) : Type :=
  sbox : A -> sBox A.

Inductive seq {A : Type} (a : A) : A -> SProp :=
  seq_refl : seq a a.
Arguments seq_refl {A} {a}.
Definition foo (x : seq O O) :=
  @eq_refl (sBox (seq 0 0)) _ : sbox _ x = sbox _ (@seq_refl nat O).

Definition seq_rect_r : forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, seq y x -> P y.
Proof. intros. destruct H. exact X. Defined.

Definition seq_rect_dep_r (A : Type) (x : A) (P : forall a : A, seq a x -> Type) :
  P x seq_refl -> forall (y : A) (e : seq y x), P y e.
Proof. intros H y e. destruct e. exact H. Defined.

(* Register seq as equations.equality.type. *)
(* Register seq_refl as equations.equality.refl. *)
(* Register seq_rect_r as equations.equality.case. *)
(* Register seq_rect_dep_r as equations.equality.elim. *)


Register Init.Logic.eq as equations.equality.type.
Register Init.Logic.eq_refl as equations.equality.refl.
Register Init.Logic.eq_rect_r as equations.equality.case.
Register Equations.DepElim.eq_rect_dep_r as equations.equality.elim.

(* FIXME *)
Register Equations.EqDec.EqDec as equations.eqdec.class.
Register Equations.EqDec.dec_eq as equations.eqdec.dec_eq.

Inductive sFalse : SProp :=.
Scheme sFalse_case := Minimality for sFalse Sort Type.
Inductive sTrue : SProp := sI.

Register sFalse as equations.bottom.type.
Register sFalse_case as equations.bottom.case.
Register sFalse_rect as equations.bottom.elim.

Register sTrue as equations.top.type.
Register sI as equations.top.intro.
Register sTrue_rect as equations.top.elim.

Inductive sand (A B : SProp) := sconj : A -> B -> sand A B.

Register sand as equations.conj.type.
Register sconj as equations.conj.intro.

Register Init.Datatypes.unit as equations.unit.type.
Register Init.Datatypes.tt as equations.unit.intro.

Register Init.Datatypes.prod as equations.product.type.
Register Init.Datatypes.pair as equations.product.intro.

Definition srelation (A : Type) := A -> A -> SProp.

Inductive sAcc {A : Type} (R : srelation A) (x : A) : Prop :=
| sAcc_intro : (forall y, R y x -> sAcc R y) -> sAcc R x.

Definition swell_founded {A} (R : srelation A) := forall x, sAcc R x.

Class SWellFounded {A : Type} (R : srelation A) :=
  swellfounded : swell_founded R.

Inductive strans_clos {A} (R : srelation A) : srelation A :=
| strans_clos_step x y : R x y -> strans_clos R x y
| strans_clos_trans x y z :
    strans_clos R x y -> strans_clos R y z -> strans_clos R x z.

Register SWellFounded as equations.wellfounded.class.
Register swell_founded as equations.wellfounded.type.
Register srelation as equations.relation.type.
Register strans_clos as equations.relation.transitive_closure.

(* Dependent elimination constants *)
Register Equations.DepElim.NoConfusionPackage as equations.noconfusion.class.
Register Equations.DepElim.apply_noConfusion as equations.depelim.apply_noConfusion.
Register Equations.DepElim.simplify_ind_pack as equations.depelim.simplify_ind_pack.

Register Equations.DepElim.simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register Equations.DepElim.opaque_ind_pack_eq_inv as equations.depelim.opaque_ind_pack_eq_inv.
Register Equations.DepElim.eq_simplification_sigma1 as equations.depelim.simpl_sigma.
Register Equations.DepElim.eq_simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register Equations.DepElim.eq_simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.
Register Equations.DepElim.pack_sigma_eq as equations.depelim.pack_sigma_eq.
Register Equations.DepElim.simplification_K as equations.depelim.simpl_K.
Register Equations.DepElim.simplification_K_dec as equations.depelim.simpl_K_dec.
Register Equations.DepElim.solution_left as equations.depelim.solution_left.
Register Equations.DepElim.solution_left_dep as equations.depelim.solution_left_dep.
Register Equations.DepElim.solution_right as equations.depelim.solution_right.
Register Equations.DepElim.solution_right_dep as equations.depelim.solution_right_dep.

(* Type parameterization *)
(*
Register Equations.Init.Id as equations.equality.type
Register Equations.Init.id_refl as equations.equality.refl
Register Equations.DepElim.Id_rect_r as equations.equality.case
Register Equations.DepElim.Id_rect_dep_r as equations.equality.elim

Register Equations.Init.Empty as equations.bottom.type

Register Init.Datatypes.unit as equations.top.type
Register Init.Datatypes.tt as equations.top.intro

(* Fixme not polymorphic *)
Register Init.Logic.and as equations.conj.type
Register Init.Logic.conj as equations.conj.intro

Register Init.Datatypes.unit as equations.unit.type
Register Init.Datatypes.tt as equations.unit.intro

(* Fixme not polymorphic *)
Register Init.Datatypes.prod as equations.product.type
Register Init.Datatypes.pair as equations.product.intro

(* FIXME not in Type *)
Register Equations.Classes.WellFounded as equations.wellfounded.class
Register Init.Wf.well_founded as equations.wellfounded.type
Register Coq.Classes.CRelationClasses.crelation as equations.relation.type
Register Equations.Classes.transitive_closure as equations.relation.transitive_closure.

Register Equations.DepElim.NoConfusionIdPackage as equations.noconfusion.class.
*)