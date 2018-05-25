(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open EConstr
open Covering

type matching_problem = pat list * pat list
type clause = rel_context * matching_problem
type problems = rel_context * clause list

val make_inversion_pb :
  Environ.env -> Evd.evar_map -> Names.inductive * EConstr.EInstance.t -> problems * constr

val find_split : rel_context ->
  (context_map * (Covering.pat list * Covering.pat list)) list -> int option

val is_prel_pat : int -> pat -> bool

val simplify_problems : Environ.env -> Evd.evar_map -> (context_map * matching_problem) list -> (context_map * matching_problem) list
val solve_problem : Environ.env -> Evd.evar_map -> constr -> problems -> Evd.evar_map * splitting

