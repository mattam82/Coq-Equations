(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open Syntax
open EConstr
open Equations_common
open Context_map

(** Programs and splitting trees *)

(** Splitting trees *)

type path_component = Id.t * bool

type path = path_component list

val path_id : path -> Id.t

module PathOT :
  sig
    type t = path
    val compare : t -> t -> int
  end
module PathMap : CSig.MapS with type key = PathOT.t

type rec_node = {
  rec_node_term : constr;
  rec_node_arg : Constrexpr.constr_expr;
  rec_node_rel : Constrexpr.constr_expr option;
  rec_node_intro : int;
  rec_node_newprob : context_map }

type splitting =
    Compute of context_map * where_clause list * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Mapping of context_map * splitting
  | RecValid of context_map * identifier * rec_node * splitting
  | Refined of context_map * refined_node * splitting

and where_clause =
  { where_program : program;
    where_program_orig : program_info;
    where_program_args : constr list; (* In original context, de Bruijn only *)
    where_path : path;
    where_orig : path;
    where_context_length : int; (* Length of enclosing context, including fixpoint prototype if any *)
    where_type : types }

and refined_node =
  { refined_obj : identifier * constr * types;
    refined_rettyp : types;
    refined_arg : int;
    refined_path : path;
    refined_term : EConstr.t;
    refined_args : constr list;
    refined_revctx : context_map;
    refined_newprob : context_map;
    refined_newprob_to_lhs : context_map;
    refined_newty : types }

and program =
  { program_info : program_info;
    program_prob : context_map;
    program_splitting : splitting;
    program_rec_node : rec_node option;
    program_term : constr }

and splitting_rhs = RProgram of constr | REmpty of int * splitting option array


val where_id : where_clause -> Id.t
val where_term : where_clause -> constr

val program_id : program -> Id.t
val program_type : program -> EConstr.t
val program_sign : program -> EConstr.rel_context
val program_impls : program -> Impargs.manual_explicitation list
val program_rec : program -> program_rec_info option

val pr_path : Evd.evar_map -> path -> Pp.t
val eq_path : path -> path -> bool

val pr_splitting : env -> Evd.evar_map -> ?verbose:bool -> splitting -> Pp.t
val ppsplit : splitting -> unit

val where_context : where_clause list -> rel_context

val pr_rec_info : program_info -> Pp.t

val context_map_of_splitting : splitting -> context_map

val helper_evar :
  Evd.evar_map ->
  Evar.t ->
  env ->
  types -> Evar_kinds.t Loc.located -> Evd.evar_map * constr

(** Compilation to Coq terms *)
val term_of_tree :
  Evd.evar_map ref ->
  env ->
  splitting ->
  constr * constr

val make_program :
  Evd.evar_map ref ->
  env ->
  rel_context ->
  program_info ->
  context_map ->
  splitting ->
  rec_node option ->
  program

val define_constants : flags ->
  Evd.evar_map ref ->
  env ->
  splitting -> (Constant.t * int) list * splitting

(** Compilation from splitting tree to terms. *)

val is_comp_obl : Evd.evar_map -> Id.t with_loc option -> Evar_kinds.t -> bool

type term_info = {
  term_id : Names.GlobRef.t;
  term_ustate : UState.t;
  term_evars : (Id.t * Constr.t) list;
  base_id : string;
  decl_kind : Decl_kinds.definition_kind;
  helpers_info : (Constant.t * int) list;
  comp_obls : Constant.t list; (** The recursive call proof obligations *)
  user_obls : Id.Set.t; (** The user proof obligations *)
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_split : splitting;
    program_split_info : term_info }

val is_polymorphic : term_info -> bool

val define_mutual_nested : Evd.evar_map ref ->
                           ('a -> EConstr.t) ->
                           (program * 'a) list ->
                           (program * 'a * EConstr.t) list *
                           (program * 'a * EConstr.constr) list


val define_tree :
  rec_type option -> rel_context -> flags ->
  (Constrexpr.explicitation * (bool * bool * bool)) list ->
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  Id.t * rel_context * types ->
  Id.t with_loc option ->
  splitting ->
  (splitting -> (Constr.t -> Constr.t) ->
   term_info ->
   UState.t -> unit) ->
  unit

val mapping_rhs : Evd.evar_map -> context_map -> splitting_rhs -> splitting_rhs
val map_rhs :
  (constr -> constr) ->
  (int -> int) -> splitting_rhs -> splitting_rhs
val map_split : (constr -> constr) -> splitting -> splitting

val simplify_evars : Evd.evar_map -> EConstr.t -> EConstr.t
