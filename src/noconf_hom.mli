(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open EConstr

val derive_no_confusion_hom :
  env -> Evd.evar_map -> polymorphic:bool -> Names.inductive * EInstance.t -> unit
