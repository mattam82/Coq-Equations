(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names

open Syntax

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

val map_ctx_map :
  (Constr.t -> Constr.t) -> context_map -> context_map

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

(** Splitting trees *)

type path = Evd.evar list

type splitting =
    Compute of context_map * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list *
      Tacmach.tactic * (Proofview.entry * Proofview.proofview) *
      (Proof_type.goal * constr list * context_map * context_map option * splitting) list
  | Mapping of context_map * splitting
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

val pr_path : Evd.evar_map -> Evd.evar list -> Pp.std_ppcmds
val eq_path : Evar.t list -> Evar.t list -> bool

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
  env ->
  Evd.evar_map ->
  rel_context ->
  Int.Set.elt ->
  Int.Set.elt -> Int.Set.t
val dependencies_of_term :
  env ->
  Evd.evar_map ->
  rel_context ->
  constr ->
  Int.Set.elt -> Int.Set.t
val non_dependent :
  ('a * 'b * constr) list -> constr -> Int.Set.t
val subst_term_in_context :
  constr -> ('a * 'b * constr) list -> ('a * 'b * constr) list
val strengthen :
  ?full:bool ->
  ?abstract:bool ->
  env ->
  Evd.evar_map ->
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

val blockers : user_pat list -> context_map -> int list
val pr_rel_name : rel_context -> int -> Pp.std_ppcmds

val subst_matches_constr :
  int -> (int * constr) list -> constr -> constr
val is_all_variables : 'a * pat list * 'b -> bool
val do_renamings : (name * 'a * 'b) list -> (name * 'a * 'b) list
val split_var :
  env * Evd.evar_map ref ->
  int ->
  rel_context ->
  (int * (name * Constr.t option * Constr.t) list *
   context_map option array)
  option
val find_empty : env * Evd.evar_map ref -> rel_context -> int option
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
