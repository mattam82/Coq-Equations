(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

val solve_subterm_tac : unit -> unit Proofview.tactic

val derive_subterm : Environ.env -> Evd.evar_map -> polymorphic:bool -> Names.inductive * EConstr.EInstance.t -> unit
val derive_below : Environ.env -> Evd.evar_map -> polymorphic:bool -> Names.inductive * EConstr.EInstance.t -> unit
