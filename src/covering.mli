(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open EConstr
open Equations_common
open Syntax

type peconstructor = Names.constructor peuniverses

(** Internal patterns *)
type pat =
    PRel of int
  | PCstr of peconstructor * pat list
  | PInac of constr
  | PHide of int


(** Substitutions *)
type context_map = rel_context * pat list * rel_context

(** Tag with a Constant.t application (needs env to infer type) *)
val mkInac : env -> esigma -> constr -> constr
val mkHide : env -> esigma -> constr -> constr

(* Constr of a pattern *)
val pat_constr : pat -> constr

(* Constr of a pattern optionally marking innaccessibles and hidden patterns
   and modifying the evar_map in this case only. *)
val constr_of_pat : ?inacc_and_hide:bool -> env -> Evd.evar_map -> pat -> Evd.evar_map * constr
val constrs_of_pats : ?inacc_and_hide:bool -> env -> Evd.evar_map -> pat list -> Evd.evar_map * constr list

(** Free pattern variables (excluding inaccessibles and hiddens) *)
val pat_vars : pat -> Int.Set.t
val pats_vars : pat list -> Int.Set.t

(** Make the terms inaccessible *)
val inaccs_of_constrs : constr list -> pat list

(** Reverse of constr_of_pat turning applications of innac/hide into 
    the proper patterns *)
val pats_of_constrs : Evd.evar_map -> constr list -> pat list
val pat_of_constr : Evd.evar_map -> constr -> pat

(** Translating back to user patterns. *)
val context_map_to_lhs : ?avoid:Id.Set.t -> ?loc:Loc.t -> context_map -> Syntax.lhs

(** Pretty-printing *)
val pr_constr_pat : env -> Evd.evar_map -> constr -> Pp.t
val pr_pat : env -> Evd.evar_map -> pat -> Pp.t
val pr_context : env -> Evd.evar_map -> rel_context -> Pp.t
val ppcontext : env -> Evd.evar_map -> rel_context -> unit
val pr_context_map : env -> Evd.evar_map -> context_map -> Pp.t
val ppcontext_map : env -> Evd.evar_map -> context_map -> unit
val ppcontext_map_empty : context_map -> unit

val typecheck_map :
  Environ.env -> Evd.evar_map -> context_map -> unit
val check_ctx_map :
  ?unsafe:bool -> Environ.env -> Evd.evar_map -> context_map -> context_map

(** Smart constructor (doing runtime checks) *)
val mk_ctx_map : ?unsafe:bool -> Environ.env ->
  Evd.evar_map ->
  rel_context ->
  pat list ->
  rel_context -> context_map

val map_ctx_map :
  (EConstr.t -> EConstr.t) -> context_map -> context_map

(** Substitution and specialization *)
val subst_pats_constr : Evd.evar_map -> int -> pat list -> constr -> constr
val subst_context : Evd.evar_map -> pat list -> rel_context -> rel_context
val specialize : Evd.evar_map -> pat list -> pat -> pat
val specialize_constr : Evd.evar_map -> pat list -> constr -> constr
val specialize_pats : Evd.evar_map -> pat list -> pat list -> pat list
val specialize_rel_context :
  Evd.evar_map -> pat list -> rel_context -> rel_context
val mapping_constr : Evd.evar_map -> context_map -> constr -> constr
val subst_constr_pat : Evd.evar_map -> int -> constr -> pat -> pat
val subst_constr_pats : Evd.evar_map -> int -> constr -> pat list -> pat list
val lift_patn : int -> int -> pat -> pat
val lift_patns : int -> int -> pat list -> pat list
val lift_pat : int -> pat -> pat
val lift_pats : int -> pat list -> pat list
val make_permutation : ?env:Environ.env -> Evd.evar_map ->
  context_map -> context_map -> context_map

(** Programs and splitting trees *)

(** Splitting trees *)

type path_component =
  | Evar of Evar.t
  | Ident of Id.t

type path = path_component list

type splitting =
    Compute of context_map * where_clause list * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list *
      Tacmach.tactic * (Proofview.entry * Proofview.proofview) *
      (Goal.goal * constr list * context_map * context_map option * splitting) list
  | Mapping of context_map * splitting
  | RecValid of identifier * splitting
  | Refined of context_map * refined_node * splitting

and where_clause =
  { where_id : identifier;
    where_path : path;
    where_orig : path;
    where_nctx : named_context;
    where_prob : context_map;
    where_arity : types; (* In nctx + pi1 prob *)
    where_term : constr; (* In original context, de Bruijn only *)
    where_type : types;
    where_splitting : splitting Lazy.t }

and refined_node = {
  refined_obj : identifier * constr * types;
  refined_rettyp : types;
  refined_arg : int;
  refined_path : path;
  refined_ex : Evar.t;
  refined_app : constr * constr list;
  refined_revctx : context_map;
  refined_newprob : context_map;
  refined_newprob_to_lhs : context_map;
  refined_newty : types;
}

and splitting_rhs = RProgram of constr | REmpty of int

val pr_path : Evd.evar_map -> path -> Pp.t
val eq_path : path -> path -> bool

val pr_splitting : env -> Evd.evar_map -> ?verbose:bool -> splitting -> Pp.t
val ppsplit : splitting -> unit

(** Covering computation *)

val context_map_of_splitting : splitting -> context_map
val specialize_mapping_constr : Evd.evar_map -> context_map -> constr -> constr
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
val is_fix_proto : Evd.evar_map -> constr -> bool
val fix_rels : Evd.evar_map -> rel_context -> Int.Set.t
val dependencies_of_rel :
  with_red:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  Int.Set.elt ->
  Int.Set.elt -> Int.Set.t
val dependencies_of_term :
  with_red:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  constr ->
  Int.Set.elt -> Int.Set.t
val non_dependent : Evd.evar_map -> 
  ('a * 'b * constr) list -> constr -> Int.Set.t
val subst_term_in_context : Evd.evar_map -> 
  constr -> rel_context -> rel_context
val strengthen :
  ?full:bool ->
  ?abstract:bool ->
  env ->
  Evd.evar_map ->
  rel_context ->
  Int.Set.elt ->
  constr ->
  context_map * (int * int) list

(* Return a substitution and its inverse. *)
(* For more flexibility, [rels] is a set of indices which are to be
 * moved before the variable. By default, this is everything already before
 * the variable. *)
val new_strengthen :
  Environ.env -> Evd.evar_map ->
  rel_context -> int -> ?rels:Int.Set.t -> constr ->
  context_map * context_map

val id_subst : 'a list -> 'a list * pat list * 'a list
val eq_context_nolet :
  env ->
  Evd.evar_map -> rel_context -> rel_context -> bool
val check_eq_context_nolet :
  env ->
  Evd.evar_map ->
  context_map ->
  context_map -> unit
val compose_subst : ?unsafe:bool -> Environ.env ->
  ?sigma:Evd.evar_map ->
  context_map ->
  context_map ->
  context_map
val push_mapping_context : Evd.evar_map ->
  rel_declaration ->
  context_map ->
  context_map
val lift_subst :
  Environ.env -> Evd.evar_map -> context_map -> rel_context -> context_map
val single_subst :
  ?unsafe:bool ->
  env ->
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
  env ->
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr ->
  constr -> context_map
val unify_constrs :
  env ->
  Evd.evar_map ->
  Int.Set.t ->
  rel_context ->
  constr list ->
  constr list -> context_map
val flexible : pat list -> 'a list -> Int.Set.t
val accessible : pat -> Int.Set.t
val accessibles : pat list -> Int.Set.t
val hidden : pat -> bool
val match_pattern : user_pat_loc -> pat ->
                    ((identifier * bool) * pat) list * (Constrexpr.constr_expr * pat) list *
                      (user_pat_loc * constr) list
val match_patterns :
  user_pats -> pat list -> ((identifier * bool) * pat) list * (Constrexpr.constr_expr * pat) list *
                                                   (user_pat_loc * constr) list
val matches :
  user_pats -> context_map -> (((identifier * bool) * pat) list * (Constrexpr.constr_expr * pat) list *                       (user_pat_loc * constr) list)  unif_result
val match_user_pattern :
  pat -> user_pat_loc -> (int * user_pat) list * (identifier * pat) list
val match_user_patterns :
  pat list ->
  user_pats -> (int * user_pat) list * (identifier * pat) list
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
  rel_context


type int_data = {
  rec_info : rec_type option;
  fixdecls : rel_context;
  intenv : Constrintern.internalization_env;
  notations : (Names.lstring * Constrexpr.constr_expr *
               Notation_term.scope_name option) list
}

val interp_program_body : Environ.env ->
           Evd.evar_map -> EConstr.rel_context ->
           Constrintern.internalization_env ->
           Syntax.program_body ->
           EConstr.types option -> Evd.evar_map * EConstr.constr

val interp_constr_in_rhs_env :Environ.env ->
           Evd.evar_map ref ->
  int_data ->
           EConstr.rel_context * Environ.env * int * EConstr.Vars.substl ->
           Syntax.program_body ->
           EConstr.t option -> EConstr.constr * EConstr.types

val interp_constr_in_rhs :
  env ->
  rel_context ->
  Evd.evar_map ref ->
  int_data ->
  constr option ->
  (Id.t * pat) list ->
  rel_context ->
  program_body -> constr * types
val unify_type :
  env ->
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

val blockers : user_pats -> context_map -> int list
val pr_rel_name : Environ.env -> int -> Pp.t

val subst_matches_constr : Evd.evar_map ->
  int -> (int * constr) list -> constr -> constr
val is_all_variables : 'a * pat list * 'b -> bool
val do_renamings : env -> Evd.evar_map -> rel_context -> rel_context

type 'a split_var_result =
  | Splitted of 'a
  | CannotSplit of Names.Name.t * rel_context * constr

val split_var :
  env * Evd.evar_map ref ->
  int ->
  rel_context ->
  (int * rel_context * context_map option array) split_var_result option
    
val find_empty : env * Evd.evar_map ref -> rel_context -> int option
val variables_of_pats : pat list -> (int * bool) list
val pats_of_variables : (int * bool) list -> pat list
val lift_rel_declaration :
  int -> rel_declaration -> rel_declaration
val lookup_named_i :
  Id.t -> named_context -> int * named_declaration
val instance_of_pats : 
  Environ.env -> 
  Evd.evar_map ->
  rel_context ->
  (int * bool) list ->
  rel_context * pat list *
  pat list
val push_rel_context_eos : rel_context -> env -> esigma -> env
val split_at_eos : Evd.evar_map ->
  named_context -> named_context * named_context
val pr_problem :
  program_info ->
  env -> Evd.evar_map -> rel_context * pat list * 'c -> Pp.t
val rel_id : (Name.t * 'a * 'b) list -> int -> Id.t
val push_named_context :
  named_context -> env -> env

val where_context : where_clause list -> rel_context

val env_of_rhs : 
           Evd.evar_map ref ->
           rel_context ->
           Environ.env ->
           (Names.Id.t * pat) list ->
           rel_declaration list ->
           rel_context *
           Environ.env * int * constr list

val covering_aux :
  env ->
  Evd.evar_map ref ->
  program_info -> int_data ->
  (pre_clause * bool) list ->
  (pre_clause * bool) list ->
  path ->
  context_map ->
  user_pats ->
  rel_context -> constr ->
  ((pre_clause * bool) list * splitting) option

val covering : ?check_unused:bool ->
  env ->
  Evd.evar_map ref ->
  program_info -> int_data ->
  pre_clause list -> path ->
  context_map -> user_pats ->
  constr -> splitting

val adjust_sign_arity : Environ.env ->
           Evd.evar_map ->
           Equations_common.rel_declaration list ->
           EConstr.types ->
           (Loc.t option * 'a list * 'b) list ->
  Evd.evar_map * EConstr.rel_context * EConstr.t *
                  (Loc.t option * 'a list * 'b) list

val compute_recinfo : program_info list -> rec_type option
val print_recinfo : program_info list -> unit
val compute_fixdecls_data :
           Environ.env ->
           Evd.evar_map ref ->
           ?data:Constrintern.internalization_env ->
           Syntax.program_info list ->
           Constrintern.internalization_env *
           Equations_common.rel_declaration list * EConstr.t list

val interp_arity : Environ.env ->
  Evd.evar_map ref ->
  bool ->
  bool option ->
  pre_equation Syntax.where_clause ->
  program_info

val coverings :
  Environ.env ->
  Evd.evar_map ref ->
  int_data ->
  Syntax.program_info list ->
  pre_equation list list ->
  (Syntax.program_info * splitting) list
