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

open Syntax
open Covering
open Splitting

type rec_type = 
  | Structural
  | Logical of rec_info
and rec_info = {
  comp : constant;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}

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
val is_structural : rec_type option -> bool
val ind_fun_tac :
  rec_type option ->
  constr ->
  term_info -> Id.t -> splitting -> 'a -> Proof_type.tactic
val mapping_rhs : context_map -> splitting_rhs -> splitting_rhs
val map_rhs :
  (constr -> constr) ->
  (int -> int) -> splitting_rhs -> splitting_rhs
val clean_clause :
  'a * 'b * 'c * splitting_rhs -> 'a * 'b * 'c * splitting_rhs
val map_evars_in_constr :
  ((Id.t -> constr) -> 'a -> 'b) -> 'a -> 'b
val map_ctx_map :
  (Constr.t -> Constr.t) ->
  rel_context * 'a * rel_context ->
  rel_context * 'a * rel_context
val map_split : (constr -> constr) -> splitting -> splitting
val map_evars_in_split :
  ((Id.t -> constr) -> constr -> constr) ->
  splitting -> splitting
val ( &&& ) : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
val array_filter_map : ('a -> 'b option) -> 'a array -> 'b array
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
val pr_path : Evd.evar_map -> Evd.evar list -> Pp.std_ppcmds
val eq_path : Evar.t list -> Evar.t list -> bool

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

val rev_assoc : ('a -> 'b -> bool) -> 'a -> ('c * 'b) list -> 'c

type equation_option = OInd | ORec | OComp | OEquations

val is_comp_obl : rec_info option -> Evar_kinds.t -> bool
val hintdb_set_transparency :
  Constant.t -> bool -> Hints.hint_db_name -> unit

(** Compilation from splitting tree to terms. *)

val define_tree :
  rec_type option ->
  (Constrexpr.explicitation * (bool * bool * bool)) list ->
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  Id.t * 'a * 'b ->
  rec_info option ->
  'c ->
  splitting ->
  (((Id.t -> constr) -> constr -> constr) ->
   (existential_key * int * Id.t) list ->
   Decl_kinds.locality -> Globnames.global_reference -> unit) ->
  unit

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
val translate_cases_pattern :
  'a -> Id.t list ref -> Glob_term.cases_pattern -> user_pat

val pr_smart_global :
  Libnames.reference Misctypes.or_by_notation -> Pp.std_ppcmds
val string_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> string
val ident_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> identifier
val ids_of_pats : pat_expr located list -> identifier list

val interp_eqn :
  identifier ->
  rec_type option ->
  'a ->
  env ->
  'b ->
  'c ->
  'd ->
  'e ->
  ((Loc.t * identifier) option * input_pats * 'f rhs as 'f) ->
  (user_pat list * 'g rhs as 'g)
val make_ref : string list -> string -> Globnames.global_reference
val fix_proto_ref : unit -> constant
val constr_of_global : Globnames.global_reference -> constr

val define_by_eqs :
  (equation_option * bool) list ->
  identifier ->
  Constrexpr.local_binder list * 'a ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * identifier) option * input_pats * 'b rhs as 'b) list ->
  unit

type equation_user_option = equation_option * bool

val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

type equation_options = (equation_option * bool) list

val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

val with_rollback : ('a -> 'b) -> 'a -> 'b

val equations :
  (equation_option * bool) list ->
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
