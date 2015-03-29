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
