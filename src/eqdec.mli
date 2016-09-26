(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

type one_inductive_info = {
  ind_name : Names.identifier;
  ind_c : Term.constr;
  ind_args : Context.rel_context;
  ind_constr : (Context.rel_context * Term.types) array;
  ind_case : Term.constr -> Term.types -> Term.constr array -> Term.constr;
}
type mutual_inductive_info = {
  mutind_params : Context.named_context;
  mutind_inds : one_inductive_info array;
}
val named_of_rel_context :
  (Names.name * Constr.constr option * Constr.constr) list ->
  Constr.constr list * Term.constr list *
  (Names.identifier * Constr.constr option * Constr.constr) list
val subst_rel_context :
  int ->
  Constr.constr list ->
  ('a * Constr.constr option * Constr.constr) list ->
  ('a * Constr.constr option * Constr.constr) list
val inductive_info :
  (Names.MutInd.t * int) * Univ.universe_instance -> mutual_inductive_info
val eq_dec_class :
  unit ->
  Context.rel_context *
  (Typeclasses.typeclass Term.puniverses * Term.constr list)
val dec_eq : unit -> Term.constr
val vars_of_pars : (Names.Id.t * 'a * 'b) list -> Term.constr array
val derive_eq_dec : Environ.env -> Evd.evar_map -> Term.pinductive -> unit
