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
open Covering
open EConstr

val helper_evar :
  Evd.evar_map ->
  Evar.t ->
  env ->
  types -> Evar_kinds.t Loc.located -> Evd.evar_map * constr

(** Compilation to Coq terms *)
val term_of_tree :
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  splitting ->
  (Evar.t * int) list * int Evar.Map.t * constr * constr


(** Compilation from splitting tree to terms. *)

val is_comp_obl : Evd.evar_map -> logical_rec option -> Evar_kinds.t -> bool

type term_info = {
  term_id : Names.GlobRef.t;
  term_ustate : UState.t;
  term_evars : (Id.t * Constr.t) list;
  base_id : string;
  decl_kind : Decl_kinds.definition_kind;
  helpers_info : (Evar.t * int * identifier) list;
  comp_obls : Id.Set.t; (** The recursive call proof obligations *)
  user_obls : Id.Set.t; (** The user proof obligations *)
}

type program_info = {
  program_id : Id.t;
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec_annot : rec_annot option;
  program_rec : Syntax.rec_type option;
  program_impls : Impargs.manual_explicitation list;
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_split : splitting;
    program_split_info : term_info }

val is_polymorphic : term_info -> bool

val define_tree :
  rec_type option -> rel_context -> Decl_kinds.polymorphic ->
  (Constrexpr.explicitation * (bool * bool * bool)) list ->
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  Id.t * rel_context * types ->
  logical_rec option ->
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
