From Equations Require Import Init.
Require Import Equations.Prop.Classes Equations.Prop.EqDec Equations.Prop.DepElim.
From Stdlib Require Import Relations.

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

Register Init.Logic.eq as equations.equality.type.
Register Init.Logic.eq_refl as equations.equality.refl.
Register Equations.Prop.Logic.transport_r as equations.equality.case.
Register Equations.Prop.Logic.eq_elim_r as equations.equality.elim.

Register Classes.EqDec as equations.eqdec.class.
Register Classes.dec_eq as equations.eqdec.dec_eq.

Register Classes.UIP as equations.uip.class.
Register Classes.uip as equations.uip.uip.

Register Init.Logic.False as equations.bottom.type.
Register Init.Logic.False_rect as equations.bottom.case.
Register Logic.False_rect_dep as equations.bottom.elim.

Register Init.Logic.True as equations.top.type.
Register Init.Logic.I as equations.top.intro.
Register Logic.True_rect_dep as equations.top.elim.

Register Init.Logic.and as equations.conj.type.
Register Init.Logic.conj as equations.conj.intro.

Register Init.Datatypes.unit as equations.unit.type.
Register Init.Datatypes.tt as equations.unit.intro.

Register Init.Datatypes.prod as equations.product.type.
Register Init.Datatypes.pair as equations.product.intro.

Register Classes.WellFounded as equations.wellfounded.class.
Register Init.Wf.well_founded as equations.wellfounded.type.
Register Relations.Relation_Definitions.relation as equations.relation.type.
Register Relation_Operators.clos_trans as equations.relation.transitive_closure.

(* Dependent elimination constants *)
Register Equations.Prop.DepElim.solution_left as equations.depelim.solution_left.
Register Equations.Prop.DepElim.solution_left_dep as equations.depelim.solution_left_dep.
Register Equations.Prop.DepElim.solution_right as equations.depelim.solution_right.
Register Equations.Prop.DepElim.solution_right_dep as equations.depelim.solution_right_dep.

Register Equations.Prop.Classes.NoConfusionPackage as equations.noconfusion.class.
Register Equations.Prop.Classes.apply_noConfusion as equations.depelim.apply_noConfusion.

Register Equations.Prop.Classes.NoCyclePackage as equations.nocycle.class.
Register Equations.Prop.Classes.apply_noCycle_left as equations.depelim.apply_noCycle_left.
Register Equations.Prop.Classes.apply_noCycle_right as equations.depelim.apply_noCycle_right.

Register Equations.Prop.DepElim.eq_simplification_sigma1 as equations.depelim.simpl_sigma.
Register Equations.Prop.DepElim.eq_simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register Equations.Prop.DepElim.eq_simplification_sigma1_nondep_dep as equations.depelim.simpl_sigma_nondep_dep.
Register Equations.Prop.DepElim.eq_simplification_sigma1_dep_dep as equations.depelim.simpl_sigma_dep_dep.

Register Equations.Prop.DepElim.simplify_ind_pack as equations.depelim.simplify_ind_pack.
Register Equations.Prop.DepElim.simplify_ind_pack_inv as equations.depelim.simplify_ind_pack_inv.
Register Equations.Prop.DepElim.opaque_ind_pack_eq_inv as equations.depelim.opaque_ind_pack_eq_inv.

Register Equations.Prop.DepElim.pack_sigma_eq as equations.depelim.pack_sigma_eq.
Register Equations.Prop.DepElim.simplification_K_uip as equations.depelim.simpl_uip.

(* Now we can use the deriving support *)

Derive Signature for eq.
