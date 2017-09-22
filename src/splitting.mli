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
open Covering
open Equations_common

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
  splitting ->
  (existential_key * int) list * int Evar.Map.t * constr * constr


(** Compilation from splitting tree to terms. *)

val is_comp_obl : logical_rec option -> Evar_kinds.t -> bool

type term_info = {
  base_id : string;
  decl_kind : Decl_kinds.definition_kind;
  helpers_info : (existential_key * int * identifier) list;
  comp_obls : Id.Set.t; (** The recursive call proof obligations *)
}

val define_tree :
  rec_type option -> Decl_kinds.polymorphic ->
  (Constrexpr.explicitation * (bool * bool * bool)) list ->
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  env ->
  Id.t * rel_context * types ->
  logical_rec option ->
  splitting ->
  (splitting -> ((Id.t -> constr) -> constr -> constr) ->
   term_info -> Globnames.global_reference ->
   Evd.evar_universe_context -> unit) ->
  unit

val mapping_rhs : context_map -> splitting_rhs -> splitting_rhs
val map_rhs :
  (constr -> constr) ->
  (int -> int) -> splitting_rhs -> splitting_rhs
val clean_clause :
  'a * 'b * 'c * splitting_rhs -> 'a * 'b * 'c * splitting_rhs
val map_evars_in_constr :
  Evd.evar_map -> ((Id.t -> constr) -> constr -> 'b) -> constr -> 'b
val map_split : (constr -> constr) -> splitting -> splitting
val map_evars_in_split :
  Evd.evar_map ->
  ((Id.t -> constr) -> constr -> constr) ->
  splitting -> splitting
