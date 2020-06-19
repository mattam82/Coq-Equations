(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Equations_common
open EConstr

type one_inductive_info = {
  ind_name : identifier;
  ind_c : constr;
  ind_args : rel_context;
  ind_constr : (rel_context * types) array;
  ind_case : constr -> types -> constr array -> constr;
}
type mutual_inductive_info = {
  mutind_params : named_context;
  mutind_inds : one_inductive_info array;
}

val inductive_info :
  Evd.evar_map -> (Names.MutInd.t * int) * EInstance.t -> mutual_inductive_info

val eq_dec_class :
  esigma ->
  rel_context *
  (Typeclasses.typeclass peuniverses * Constr.t list)

val dec_eq : esigma -> constr

val vars_of_pars : named_context -> constr array

val derive_eq_dec : Environ.env -> Evd.evar_map -> poly:bool ->
                    Names.inductive * EInstance.t -> unit
