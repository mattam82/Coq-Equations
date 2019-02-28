From Equations Require Import Init Classes DepElim FunctionalInduction.
From Coq Require Import Relations.

(** Naturals *)
Register Init.Datatypes.O as equations.nat.zero.
Register Init.Datatypes.S as equations.nat.succ.
Register Init.Datatypes.nat as equations.nat.type.

(* Sigma Types *)
Register Equations.Init.sigma as equations.sigma.type.
Register Equations.Init.sigmaI as equations.sigma.intro.
Register Equations.Init.pr1 as equations.sigma.pr1.
Register Equations.Init.pr2 as equations.sigma.pr2.

(** Classes *)
Register Equations.FunctionalInduction.FunctionalInduction as equations.funind.class.
Register Equations.FunctionalInduction.FunctionalElimination as equations.funelim.class.
Register Equations.DepElim.DependentEliminationPackage as equations.depelim.class.
Register Equations.Classes.ImpossibleCall as equations.impossiblecall.class.

Register Equations.Signature.Signature as equations.signature.class.
Register Equations.Signature.signature as equations.signature.signature.
Register Equations.Signature.signature_pack as equations.signature.pack.

(** Internally used constants *)

Register Equations.Init.fixproto as equations.fixproto.
Register Equations.Init.hidebody as equations.internal.hidebody.
Register Equations.Init.bang as equations.internal.bang.
Register Equations.Init.inaccessible_pattern as equations.internal.inaccessible_pattern.
Register Equations.DepElim.block as equations.internal.block.
Register Equations.DepElim.hide_pattern as equations.internal.hide_pattern.
Register Equations.DepElim.add_pattern as equations.internal.add_pattern.
Register Equations.DepElim.the_end_of_the_section as equations.internal.the_end_of_the_section.
Register Equations.DepElim.end_of_section as equations.internal.end_of_section.

(** Logic parameterization *)

Register Init.Logic.eq as equations.equality.type.
Register Init.Logic.eq_refl as equations.equality.refl.
Register Init.Logic.eq_rect_r as equations.equality.case.
Register Equations.DepElim.eq_rect_dep_r as equations.equality.elim.

Register Equations.EqDec.EqDec as equations.eqdec.class.
Register Equations.EqDec.dec_eq as equations.eqdec.dec_eq.

Register Equations.EqDec.UIP as equations.uip.class.
Register Equations.EqDec.uip as equations.uip.uip.

Register Init.Logic.False as equations.bottom.type.
Register Init.Logic.False_rect as equations.bottom.case.
Register Equations.DepElim.False_rect_dep as equations.bottom.elim.

Register Init.Logic.True as equations.top.type.
Register Init.Logic.I as equations.top.intro.
Register Equations.DepElim.True_rect_dep as equations.top.elim.

Register Init.Logic.and as equations.conj.type.
Register Init.Logic.conj as equations.conj.intro.

Register Init.Datatypes.unit as equations.unit.type.
Register Init.Datatypes.tt as equations.unit.intro.

Register Init.Datatypes.prod as equations.product.type.
Register Init.Datatypes.pair as equations.product.intro.

Register Equations.Classes.WellFounded as equations.wellfounded.class.
Register Init.Wf.well_founded as equations.wellfounded.type.
Register Relations.Relation_Definitions.relation as equations.relation.type.
Register Relations.Relation_Operators.clos_trans as equations.relation.transitive_closure.

(* Dependent elimination constants *)
Register Equations.Classes.NoConfusionPackage as equations.noconfusion.class.
Register Equations.Classes.apply_noConfusion as equations.depelim.apply_noConfusion.

Register Equations.Classes.NoCyclePackage as equations.nocycle.class.
Register Equations.Classes.apply_noCycle_left as equations.depelim.apply_noCycle_left.
Register Equations.Classes.apply_noCycle_right as equations.depelim.apply_noCycle_right.

Register Equations.DepElim.simplify_ind_pack as equations.depelim.simplify_ind_pack.
Register Equations.DepElim.simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register Equations.DepElim.opaque_ind_pack_eq_inv as equations.depelim.opaque_ind_pack_eq_inv.
Register Equations.DepElim.eq_simplification_sigma1 as equations.depelim.simpl_sigma.
Register Equations.DepElim.eq_simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register Equations.DepElim.eq_simplification_sigma1_nondep_dep as equations.depelim.simpl_sigma_nondep_dep.
Register Equations.DepElim.eq_simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.
Register Equations.DepElim.pack_sigma_eq as equations.depelim.pack_sigma_eq.
Register Equations.DepElim.simplification_K_uip as equations.depelim.simpl_uip.
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

Derive Signature for eq.