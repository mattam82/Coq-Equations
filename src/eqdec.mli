(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Equations_common

type one_inductive_info = {
  ind_name : Names.identifier;
  ind_c : Term.constr;
  ind_args : rel_context;
  ind_constr : (rel_context * Term.types) array;
  ind_case : Term.constr -> Term.types -> Term.constr array -> Term.constr;
}
type mutual_inductive_info = {
  mutind_params : named_context;
  mutind_inds : one_inductive_info array;
}

val inductive_info :
  (Names.MutInd.t * int) * Univ.universe_instance -> mutual_inductive_info

val eq_dec_class :
  unit ->
  rel_context *
  (Typeclasses.typeclass Term.puniverses * Term.constr list)

val dec_eq : unit -> Term.constr

val vars_of_pars : named_context -> Term.constr array

val derive_eq_dec : Environ.env -> Evd.evar_map -> Term.pinductive -> unit
