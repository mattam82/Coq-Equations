Set Warnings "-notation-overridden".

From Equations Require Import Init.
Require Import Equations.Type.Logic Equations.Type.DepElim
        Equations.Type.EqDec Equations.Type.Classes.
From Coq Require Import CRelationClasses Relations.

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

Register DepElim.DependentEliminationPackage as equations.depelim.class.
Register Classes.ImpossibleCall as equations.impossiblecall.class.

(** Logic parameterization *)

Derive Signature for Id.

Register Logic.Id as equations.equality.type.
Register Logic.id_refl as equations.equality.refl.
Register Logic.Id_case as equations.equality.case.
Register Logic.Id_rect_r as equations.equality.elim.

Register Classes.EqDec as equations.eqdec.class.
Register Classes.dec_eq as equations.eqdec.dec_eq.

Register Logic.Empty as equations.bottom.type.
Register Logic.Empty_case as equations.bottom.case.
Register Logic.Empty_rect as equations.bottom.elim.

Register Coq.Init.Datatypes.unit as equations.top.type.
Register Coq.Init.Datatypes.tt as equations.top.intro.
Register Coq.Init.Datatypes.unit_rect as equations.top.elim.

Register Logic.prod as equations.conj.type.
Register Equations.Init.sigmaI as equations.conj.intro.

Register Init.Datatypes.unit as equations.unit.type.
Register Init.Datatypes.tt as equations.unit.intro.

Register Logic.prod as equations.product.type.
Register Equations.Init.sigmaI as equations.product.intro.

(* FIXME not polymorphic *)
Register Classes.WellFounded as equations.wellfounded.class.
Register WellFounded.well_founded as equations.wellfounded.type.
Register Relation.relation as equations.relation.type.
Register Relation.trans_clos as equations.relation.transitive_closure.

(* Dependent elimination constants *)

Register DepElim.solution_left as equations.depelim.solution_left.
Register DepElim.solution_left_dep as equations.depelim.solution_left_dep.
Register DepElim.solution_right as equations.depelim.solution_right.
Register DepElim.solution_right_dep as equations.depelim.solution_right_dep.

Register Classes.NoConfusionPackage as equations.noconfusion.class.
Register Classes.apply_noConfusion as equations.depelim.apply_noConfusion.

Register Classes.NoCyclePackage as equations.nocycle.class.
Register Classes.apply_noCycle_left as equations.depelim.apply_noCycle_left.
Register Classes.apply_noCycle_right as equations.depelim.apply_noCycle_right.

Register DepElim.simplification_sigma1 as equations.depelim.simpl_sigma.
Register DepElim.simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register DepElim.simplification_sigma1_nondep_dep as equations.depelim.simpl_sigma_nondep_dep.
Register DepElim.simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.

Register DepElim.simplify_ind_pack as equations.depelim.simplify_ind_pack.
Register DepElim.simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register DepElim.opaque_ind_pack_inv as equations.depelim.opaque_ind_pack_eq_inv.

Register DepElim.pack_sigma as equations.depelim.pack_sigma_eq.
Register DepElim.simplification_K_uip as equations.depelim.simpl_K.
