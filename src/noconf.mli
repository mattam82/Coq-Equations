(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Declarations
open Names
open Constr
open Context
val mkcase :
  env ->
  constr ->
  constr ->
  ((MutInd.t * int) * Univ.universe_instance ->
   int ->
   Id.t -> int -> Context.Rel.t -> types -> constr) ->
  constr
(* val mk_eqs : *)
(*   env -> *)
(*   Evd.evar_map ref -> *)
(*   constr list -> constr list -> Constr.constr -> types *)
val derive_no_confusion :
  env -> Evd.evar_map -> Term.pinductive -> unit
