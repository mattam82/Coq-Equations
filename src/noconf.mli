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

val mkcase :
  env -> Evd.evar_map ->
  constr ->
  constr ->
  ((MutInd.t * int) * EInstance.t ->
   int ->
   Id.t -> int -> rel_context -> types -> constr) ->
  constr

val derive_no_confusion :
  env -> Evd.evar_map -> polymorphic:bool -> Names.inductive * EInstance.t -> unit
