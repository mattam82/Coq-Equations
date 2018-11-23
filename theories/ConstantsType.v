From Equations Require Import Init DepElim FunctionalInduction Classes.

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

(* FIXME not polymorphic *)
Register Equations.DepElim.ImpossibleCall as equations.impossiblecall.class.

Register Equations.Signature.Signature as equations.signature.class.
Register Equations.Signature.signature as equations.signature.signature.
Register Equations.Signature.signature_pack as equations.signature.pack.

(** Internally used constants. FIXME not polymorphic *)

Register Equations.Init.fixproto as equations.fixproto.
Register Equations.Init.hidebody as equations.internal.hidebody.
Register Equations.DepElim.inaccessible_pattern as equations.internal.inaccessible_pattern.
Register Equations.DepElim.block as equations.internal.block.
Register Equations.DepElim.hide_pattern as equations.internal.hide_pattern.
Register Equations.DepElim.add_pattern as equations.internal.add_pattern.
Register Equations.DepElim.the_end_of_the_section as equations.internal.the_end_of_the_section.
Register Equations.DepElim.end_of_section as equations.internal.end_of_section.

(** Logic parameterization *)

Register Equations.Init.Id as equations.equality.type.
Register Equations.Init.id_refl as equations.equality.refl.
Register Equations.DepElim.Id_rect_r as equations.equality.case.
Register Equations.DepElim.Id_rect_dep_r as equations.equality.elim.

Register Equations.HSets.HSet as equations.eqdec.class.
Register Equations.HSets.dec_eq as equations.eqdec.dec_eq.

Register Equations.Init.Empty as equations.bottom.type.
Register Equations.Init.Empty_case as equations.bottom.case.
Register Equations.Init.Empty_rect as equations.bottom.elim.

Register Coq.Init.Datatypes.unit as equations.top.type.
Register Coq.Init.Datatypes.tt as equations.top.intro.
Register Coq.Init.Datatypes.unit_rect as equations.top.elim.

Register Equations.Init.prod as equations.conj.type.
Register Equations.Init.sigmaI as equations.conj.intro.

Register Init.Datatypes.unit as equations.unit.type.
Register Init.Datatypes.tt as equations.unit.intro.

Register Equations.Init.prod as equations.product.type.
Register Equations.Init.sigmaI as equations.product.intro.

(* FIXME not polymorphic *)
Register Equations.Classes.WellFounded as equations.wellfounded.class.
Register Init.Wf.well_founded as equations.wellfounded.type.
Register Coq.Classes.CRelationClasses.crelation as equations.relation.type.
Register Relations.Relation_Operators.clos_trans as equations.relation.transitive_closure.

(* Dependent elimination constants *)
Register Equations.DepElim.NoConfusionIdPackage as equations.noconfusion.class.
Register Equations.DepElim.apply_noConfusionId as equations.depelim.apply_noConfusion.

Register Equations.DepElim.Id_simplify_ind_pack as equations.depelim.simplify_ind_pack.
Register Equations.DepElim.Id_simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register Equations.DepElim.opaque_ind_pack_Id_inv as equations.depelim.opaque_ind_pack_eq_inv.

Register Equations.DepElim.Id_simplification_sigma1 as equations.depelim.simpl_sigma.
Register Equations.DepElim.Id_simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register Equations.DepElim.Id_simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.
Register Equations.DepElim.pack_sigma_Id as equations.depelim.pack_sigma_eq.
(* Register Equations.DepElim.Id_simplification_K as equations.depelim.simpl_K. *)
Register Equations.DepElim.Id_simplification_K as equations.depelim.simpl_K_dec.
Register Equations.DepElim.Id_solution_left as equations.depelim.solution_left.
Register Equations.DepElim.Id_solution_left_dep as equations.depelim.solution_left_dep.
Register Equations.DepElim.Id_solution_right as equations.depelim.solution_right.
Register Equations.DepElim.Id_solution_right_dep as equations.depelim.solution_right_dep.
