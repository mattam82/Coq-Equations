(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names

open Equations_common
open Syntax
open Covering
open Splitting

val make_ref : string list -> string -> Globnames.global_reference
val fix_proto_ref : unit -> constant
val constr_of_global : Globnames.global_reference -> constr

val define_by_eqs :
  Syntax.equation_option list ->
  Syntax.pre_equations ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  unit

type program_info = {
  program_id : Id.t;
  program_sign : rel_context;
  program_arity : Constr.t;
  program_oarity : Constr.t;
  program_rec : Syntax.rec_type option;
  program_impls : Impargs.manual_explicitation list;
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_cmap : (Id.t -> Constr.t) -> Constr.t -> Constr.t;
    program_split : splitting;
    program_split_info : Splitting.term_info }

type flags = {
  polymorphic : bool;
  with_eqns : bool;
  with_ind : bool }  

val define_principles :
  flags ->
  Constr.t list ->
  (program_info * compiled_program_info) list -> unit
  
val with_rollback : ('a -> 'b) -> 'a -> 'b

val equations :
  Syntax.equation_option list ->
  Syntax.pre_equations ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  unit

val solve_equations_goal :
  Proof_type.tactic ->
  Proof_type.tactic ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val dependencies :
  env ->
  constr -> named_context -> Id.Set.t * Idset.t


