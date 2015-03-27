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

(** User-level patterns *)
type user_pat =
    PUVar of identifier
  | PUCstr of constructor * int * user_pat list
  | PUInac of Constrexpr.constr_expr
type user_pats = user_pat list

(** Internal patterns *)
type pat =
    PRel of int
  | PCstr of pconstructor * pat list
  | PInac of constr
  | PHide of int

(** Substitutions *)
type context_map = rel_context * pat list * rel_context

(** Tag with a constant application (needs env to infer type) *)
val mkInac : env -> constr -> constr
val mkHide : env -> constr -> constr

(* Constr of a pattern *)
val pat_constr : pat -> constr

(* Constr of a pattern marking innaccessibles *)
val constr_of_pat : ?inacc:bool -> env -> pat -> constr
val constrs_of_pats : ?inacc:bool -> env -> pat list -> constr list

(** Free pattern variables (excluding inaccessibles and hiddens) *)
val pat_vars : pat -> Int.Set.t
val pats_vars : pat list -> Int.Set.t

(** Make the terms inaccessible *)
val inaccs_of_constrs : constr list -> pat list

(** Reverse of constr_of_pat turning applications of innac/hide into 
    the proper patterns *)
val pats_of_constrs : constr list -> pat list
val pat_of_constr : constr -> pat

(** Pretty-printing *)
val pr_constr_pat : env -> constr -> Pp.std_ppcmds
val pr_pat : env -> pat -> Pp.std_ppcmds
val pr_context : env -> rel_context -> Pp.std_ppcmds
val ppcontext : rel_context -> unit
val pr_context_map : env -> context_map -> Pp.std_ppcmds
val ppcontext_map : context_map -> unit
val typecheck_map :
  Evd.evar_map -> context_map -> unit
val check_ctx_map :
  Evd.evar_map -> context_map -> context_map

(** Smart constructor (doing runtime checks) *)
val mk_ctx_map :
  Evd.evar_map ->
  rel_context ->
  pat list ->
  rel_context -> context_map

(** Substitution and specialization *)
val subst_pats_constr : int -> pat list -> constr -> constr
val subst_context :
  pat list ->  rel_context ->
  rel_context
val specialize : pat list -> pat -> pat
val specialize_constr : pat list -> constr -> constr
val specialize_pats : pat list -> pat list -> pat list
val specialize_rel_context :
  pat list -> rel_context -> rel_context
val mapping_constr : context_map -> constr -> constr
val subst_constr_pat : int -> constr -> pat -> pat
val subst_constr_pats : int -> constr -> pat list -> pat list
val subst_rel_context :
  int ->
  constr ->
  rel_context ->
  rel_context
val subst_telescope :
  constr ->
  rel_context ->
  rel_context
val subst_in_ctx :
  int -> constr -> rel_context -> rel_context
val set_in_ctx :
  int -> constr -> rel_context -> rel_context
val lift_patn : int -> int -> pat -> pat
val lift_patns : int -> int -> pat list -> pat list
val lift_pat : int -> pat -> pat
val lift_pats : int -> pat list -> pat list

(** Programs and splitting trees *)

(** Globalized syntax *)

type program = signature * clause list

and signature = identifier * rel_context * constr (* f : Π Δ. τ *)

and clause = lhs * clause rhs (* lhs rhs *)
and lhs = user_pats (* p1 ... pn *)
and 'a rhs =
    Program of Constrexpr.constr_expr
  | Empty of identifier Loc.located
  | Rec of identifier Loc.located * Constrexpr.constr_expr option *
      'a list
  | Refine of Constrexpr.constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) Util.union *
      'a list


val pr_user_pat : env -> user_pat -> Pp.std_ppcmds
val pr_user_pats : env -> user_pat list -> Pp.std_ppcmds

val pr_lhs : env -> user_pat list -> Pp.std_ppcmds
val pplhs : user_pat list -> unit
val pr_rhs : env -> ((user_pat list * 'a) rhs as 'a) -> Pp.std_ppcmds
val pr_clause :
  env -> (user_pat list * 'a rhs as 'a) -> Pp.std_ppcmds
val pr_clauses :
  env -> (user_pat list * 'a rhs as 'a) list -> Pp.std_ppcmds
val ppclause : (user_pat list * 'a rhs as 'a) -> unit
val pr_rel_name : rel_context -> int -> Pp.std_ppcmds

(** Splitting trees *)

type path = Evd.evar list

type splitting =
    Compute of context_map * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list *
      Tacmach.tactic * (Proofview.entry * Proofview.proofview) *
      (Proof_type.goal * constr list * context_map * splitting) list
  | RecValid of identifier * splitting
  | Refined of context_map * refined_node * splitting

and refined_node = {
  refined_obj : identifier * constr * types;
  refined_rettyp : types;
  refined_arg : int;
  refined_path : path;
  refined_ex : existential_key;
  refined_app : constr * constr list;
  refined_revctx : context_map;
  refined_newprob : context_map;
  refined_newprob_to_lhs : context_map;
  refined_newty : types;
}

and splitting_rhs = RProgram of constr | REmpty of int

val pr_splitting : env -> splitting -> Pp.std_ppcmds
val ppsplit : splitting -> unit

(** Covering computation *)

val specialize_mapping_constr : context_map -> constr -> constr
val rels_of_tele : 'a list -> constr list
val patvars_of_tele : 'a list -> pat list
val pat_vars_list : int -> pat list
val intset_of_list : Int.Set.elt list -> Int.Set.t
val split_context : int -> 'a list -> 'a list * 'a * 'a list
val split_tele :
  int ->
  rel_context ->
  rel_context * rel_declaration *
    rel_context
val rels_above : 'a list -> int -> Int.Set.t
val is_fix_proto : constr -> bool
val fix_rels : ('a * 'b * constr) list -> Int.Set.t
val dependencies_of_rel :
  rel_context ->
  Int.Set.elt -> Int.Set.t
val dependencies_of_term :
  rel_context ->
  constr -> Int.Set.t
val non_dependent :
  ('a * 'b * constr) list -> constr -> Int.Set.t
val subst_term_in_context :
  constr -> ('a * 'b * constr) list -> ('a * 'b * constr) list
val strengthen :
  ?full:bool ->
  ?abstract:bool ->
  rel_context ->
  Int.Set.elt ->
  constr ->
  context_map * (int * int) list
val id_subst : 'a list -> 'a list * pat list * 'a list
val eq_context_nolet :
  env ->
  Evd.evar_map -> rel_context -> rel_context -> bool
val check_eq_context_nolet :
  env ->
  Evd.evar_map ->
  context_map ->
  context_map -> unit
val compose_subst :
  ?sigma:Evd.evar_map ->
  context_map ->
  context_map ->
  context_map
val push_mapping_context :
  rel_declaration ->
  context_map ->
  context_map
val lift_subst :
  Evd.evar_map -> context_map -> rel_context -> context_map
val single_subst :
  Evd.evar_map ->
  Int.Set.elt ->
  pat ->
  rel_context -> context_map

(* Unification *)

exception Conflict
exception Stuck
type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
type unification_result = (context_map * int * constr * pat) option

val unify :
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr ->
  constr -> context_map
val unify_constrs :
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr list ->
  constr list -> context_map
val flexible : pat list -> 'a list -> Int.Set.t
val accessible : pat -> Int.Set.t
val accessibles : pat list -> Int.Set.t
val hidden : pat -> bool
val match_pattern : user_pat -> pat -> (identifier * pat) list
val match_patterns :
  user_pat list -> pat list -> (identifier * pat) list
val matches :
  user_pats -> context_map -> (identifier * pat) list unif_result
val match_user_pattern :
  pat -> user_pat -> (int * user_pat) list * (identifier * pat) list
val match_user_patterns :
  pat list ->
  user_pat list -> (int * user_pat) list * (identifier * pat) list
val matches_user :
  context_map ->
  user_pats ->
  ((int * user_pat) list * (identifier * pat) list) unif_result
val lets_of_ctx :
  env ->
  rel_context ->
  Evd.evar_map ref ->
  (Id.t * pat) list ->
  constr list *
  rel_context *
  (name * Constr.t option * Constr.t) list
val interp_constr_in_rhs :
  env ->
  rel_context ->
  Evd.evar_map ref ->
  'a * 'b * Constrintern.internalization_env ->
  constr option ->
  (Id.t * pat) list ->
  rel_context ->
  Constrexpr.constr_expr -> constr * types
val unify_type :
  Evd.evar_map ref ->
  rel_context ->
  'a ->
  types ->
  rel_context ->
  (constr *
   ((context_map) * int *
    constr * pat)
   unif_result array)
  option

val blockers : user_pat list -> context_map -> int list

val subst_matches_constr :
  int -> (int * constr) list -> constr -> constr
val is_all_variables : 'a * pat list * 'b -> bool
val do_renamings : (name * 'a * 'b) list -> (name * 'a * 'b) list
val split_var :
  'a * Evd.evar_map ref ->
  int ->
  rel_context ->
  (int * (name * Constr.t option * Constr.t) list *
   context_map option array)
  option
val find_empty : 'a * Evd.evar_map ref -> rel_context -> int option
val rel_of_named_context :
  named_context ->
  rel_context * Id.t list
val variables_of_pats : pat list -> (int * bool) list
val pats_of_variables : (int * bool) list -> pat list
val lift_rel_declaration :
  int ->
  rel_declaration ->
  rel_declaration
val named_of_rel_context :
  rel_context ->
  constr list *
  named_context
val lookup_named_i :
  Id.t -> (Id.t * 'a * 'b) list -> int * (Id.t * 'a * 'b)
val instance_of_pats :
  'a ->
  'b ->
  rel_context ->
  (int * bool) list ->
  rel_context * pat list *
  pat list
val push_rel_context_eos : rel_context -> env -> env
val split_at_eos :
  ('a * 'b * constr) list ->
  ('a * 'b * constr) list * ('a * 'b * constr) list
val pr_problem :
  Id.t * 'a * 'b ->
  env -> rel_context * pat list * 'c -> Pp.std_ppcmds
val rel_id : (Name.t * 'a * 'b) list -> int -> Id.t
val push_named_context :
  named_context -> env -> env

val covering_aux :
  env ->
  Evd.evar_map ref ->
  identifier * bool * Constrintern.internalization_env ->
  ((user_pats * 'a rhs as 'a) * bool) list ->
  ('a * bool) list ->
  Evd.evar list ->
  context_map ->
  rel_context -> constr -> splitting option

val covering :
  env ->
  Evd.evar_map ref ->
  identifier * bool * Constrintern.internalization_env ->
  clause list ->
  context_map ->
  constr -> splitting

val helper_evar :
  Evd.evar_map ->
  Evd.evar ->
  env ->
  types -> Loc.t * Evar_kinds.t -> Evd.evar_map * constr

(** Compilation to Coq terms *)
val term_of_tree :
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  'a * 'b * 'c ->
  'd ->
  splitting ->
  (existential_key * int) list * Evar.Set.t * constr * constr

(** Raw syntax *)
type 'a located = 'a Loc.located
type pat_expr =
    PEApp of Libnames.reference Misctypes.or_by_notation located *
      pat_expr located list
  | PEWildcard
  | PEInac of Constrexpr.constr_expr
  | PEPat of Constrexpr.cases_pattern_expr
type user_pat_expr = pat_expr located
type user_pat_exprs = user_pat_expr located
type input_pats =
    SignPats of user_pat_expr list
  | RefinePats of user_pat_expr list
type pre_equation =
    identifier located option * input_pats * pre_equation rhs
val next_ident_away : Id.t -> Id.t list ref -> Id.t
type rec_type = Structural | Logical of rec_info
and rec_info = {
  comp : constant;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}


val lift_constrs : int -> constr list -> constr list
val array_remove_last : 'a array -> 'a array
val array_chop_last : 'a array -> 'a array * 'a array

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
