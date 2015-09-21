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


(** Compilation from splitting tree to terms. *)

val is_comp_obl : rec_info option -> Evar_kinds.t -> bool

val define_tree :
  rec_type option -> Decl_kinds.polymorphic ->
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

val mapping_rhs : context_map -> splitting_rhs -> splitting_rhs
val map_rhs :
  (constr -> constr) ->
  (int -> int) -> splitting_rhs -> splitting_rhs
val clean_clause :
  'a * 'b * 'c * splitting_rhs -> 'a * 'b * 'c * splitting_rhs
val map_evars_in_constr :
  Evd.evar_map ref -> ((Id.t -> constr) -> 'a -> 'b) -> 'a -> 'b
val map_split : (constr -> constr) -> splitting -> splitting
val map_evars_in_split :
  Evd.evar_map ref ->
  ((Id.t -> constr) -> constr -> constr) ->
  splitting -> splitting
