(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open EConstr

val derive_noConfusion_package :
  Environ.env ->
  Evd.evar_map ->
  poly:bool ->
  Names.inductive * EConstr.EInstance.t ->
  Names.Id.t ->
  prefix:string ->
  tactic:unit Proofview.tactic ->
  Names.Constant.t -> unit

val derive_no_confusion_hom :
  env -> Evd.evar_map -> poly:bool -> Names.inductive * EInstance.t ->
  Declare.Proof.t option
