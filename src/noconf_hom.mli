(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open EConstr

val derive_noConfusion_package :
  Environ.env ->
  Evd.evar_map ->
  Decl_kinds.polymorphic ->
  Names.inductive * EConstr.EInstance.t ->
  Names.Id.t ->
  prefix:string ->
  tactic:unit Proofview.tactic ->
  Names.Constant.t -> unit

val derive_no_confusion_hom :
  env -> Evd.evar_map -> polymorphic:bool -> Names.inductive * EInstance.t ->
  Proof_global.t option
