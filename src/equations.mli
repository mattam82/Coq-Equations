(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names

open Equations_common
open Syntax
open Covering
open Splitting

val abstract_rec_calls :
  ?do_subst:bool ->
  rec_type option ->
  int ->
  (constr * constr option * int * constr) list ->
  constr -> rel_context * int * constr
val below_transparent_state : unit -> transparent_state


val simpl_star : Proof_type.tactic
val eauto_with_below : Hints.hint_db_name list -> Tacmach.tactic
val simp_eqns : Hints.hint_db_name list -> Proof_type.tactic
val simp_eqns_in :
  Locus.clause -> Hints.hint_db_name list -> Proof_type.tactic
val autorewrites : string -> Proof_type.tactic
val autorewrite_one : string -> Proofview.V82.tac

type term_info = {
  base_id : string;
  polymorphic : bool;
  helpers_info : (existential_key * int * identifier) list;
}

(** Generation of equations and inductive graph *)

type statement = constr * types option
type statements = statement list

val find_helper_info :
  term_info -> constr -> existential_key * int * identifier
val find_helper_arg :
  term_info -> constr -> 'a array -> existential_key * 'a
val find_splitting_var : pat list -> int -> constr list -> Id.t
val intros_reducing : Proof_type.tactic
val aux_ind_fun : term_info -> splitting -> Proof_type.tactic
val ind_fun_tac :
  rec_type option ->
  constr ->
  term_info -> Id.t -> splitting -> 'a -> Proof_type.tactic
val subst_rec_split :
  bool ->
  constr ->
  context_map ->
  (Id.t * constr) list -> splitting -> splitting

val subst_app :
  constr ->
  (int -> constr -> constr array -> constr) ->
  constr -> constr
val subst_comp_proj :
  constr -> constr -> constr -> constr
val subst_comp_proj_split :
  constr -> constr -> splitting -> splitting
val reference_of_id : Id.t -> Libnames.reference
val clear_ind_assums :
  mutual_inductive -> rel_context -> rel_context
val unfold : evaluable_global_reference -> Proof_type.tactic
val ind_elim_tac :
  constr ->
  'a ->
  term_info -> Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

(** Defining equations *)
val build_equations :
  bool ->
  env ->
  Id.t ->
  term_info ->
  'a ->
  rel_context ->
  rec_type option ->
  types ->
  constant ->
  constr ->
  ?alias:constr * constr * splitting ->
  context_map -> splitting -> unit


val hintdb_set_transparency :
  Constant.t -> bool -> Hints.hint_db_name -> unit

val conv_proj_call :
  constr -> constant -> constr -> constr
val convert_projection :
  constr ->
  constant ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val unfold_constr : constr -> Proof_type.tactic
val simpl_except : Idset.t * Cset.t -> Closure.RedFlags.reds
val simpl_of : constant list -> (unit -> unit) * (unit -> unit)

(** Unfolding lemma tactic *)

val prove_unfolding_lemma :
  term_info ->
  constr ->
  constant ->
  constant ->
  splitting -> Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma

val update_split :
  rec_type option ->
  ((Id.t -> constr) -> constr -> constr) ->
  constr ->
  context_map ->
  Id.t -> splitting -> splitting

val make_ref : string list -> string -> Globnames.global_reference
val fix_proto_ref : unit -> constant
val constr_of_global : Globnames.global_reference -> constr

val define_by_eqs :
  Syntax.equation_option list ->
  identifier ->
  Constrexpr.local_binder list * 'a ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * identifier) option * input_pats * 'b rhs as 'b) list ->
  unit

val with_rollback : ('a -> 'b) -> 'a -> 'b

val equations :
  Syntax.equation_option list ->
  Loc.t * identifier ->
  Constrexpr.local_binder list * 'a ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * identifier) option * input_pats * 'b rhs as 'b) list ->
  unit


val solve_equations_goal :
  Proof_type.tactic ->
  Proof_type.tactic ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val dependencies :
  env ->
  constr -> named_context -> Id.Set.t * Idset.t
