(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr
open Environ
open Evd
open Names
open Equations_common

type 'a with_loc = Loc.t option * 'a

(** User-level patterns *)
type provenance = 
  | User
  | Generated
  | Implicit

type rec_annotation =
  | Nested
  | Mutual

type user_rec_annot = rec_annotation option

type identifier = Names.Id.t

type user_pat =
    PUVar of identifier * provenance
  | PUCstr of constructor * int * user_pats
  | PUInac of Glob_term.glob_constr
  | PUEmpty
and user_pat_loc = (user_pat, [ `any ]) DAst.t
and user_pats = user_pat_loc list

(** Raw syntax *)
type pat_expr =
    PEApp of Libnames.qualid Constrexpr.or_by_notation with_loc *
      pat_expr with_loc list
  | PEWildcard
  | PEInac of Constrexpr.constr_expr

type user_pat_expr = pat_expr with_loc

type 'a input_pats =
    SignPats of 'a
  | RefinePats of 'a list

(** Globalized syntax *)

type rec_arg = int * Id.t with_loc option
    
type rec_annot =
  | MutualOn of rec_arg option
  | NestedOn of rec_arg option
  | NestedNonRec

type program_body =
  | ConstrExpr of Constrexpr.constr_expr
  | GlobConstr of Glob_term.glob_constr
  | Constr of EConstr.constr (* We interpret a constr by substituting
                                [Var names] of the lhs bound variables
                                with the proper de Bruijn indices *)

type lhs = user_pats (* p1 ... pn *)
and ('a,'b) rhs_aux =
    Program of program_body * 'a wheres
  | Empty of identifier with_loc
  | Refine of Constrexpr.constr_expr list * 'b list
and ('a,'b) rhs = ('a, 'b) rhs_aux option
and pre_prototype =
  identifier with_loc * Constrexpr.sort_poly_decl_expr option * user_rec_annot * 
  Constrexpr.local_binder_expr list * Constrexpr.constr_expr option *
  (Id.t with_loc option, Constrexpr.constr_expr * Constrexpr.constr_expr option) by_annot option

and ('a, 'b) by_annot =
  | Structural of 'a
  | WellFounded of 'b

and 'a where_clause = pre_prototype * 'a list
and 'a wheres = 'a where_clause list * Vernacexpr.notation_declaration list
type program = (signature * clause list) list
and signature = identifier * rel_context * constr (* f : Π Δ. τ *)
and clause = Clause of Loc.t option * lhs * (clause, clause) rhs (* lhs rhs *)

type pre_equation = Pre_equation of Constrexpr.constr_expr input_pats * (pre_equation, pre_equation) rhs

type pre_clause = Pre_clause of Loc.t option * lhs * (pre_equation, pre_clause) rhs

type pre_equations = pre_equation where_clause list

(* val pr_user_pat : env -> user_pat -> Pp.t *)

val pr_provenance : with_gen:bool -> Pp.t -> provenance -> Pp.t

val pr_user_pats : ?with_gen:bool -> env -> evar_map -> user_pats -> Pp.t

val pr_lhs : env -> evar_map -> user_pats -> Pp.t
val pplhs : user_pats -> unit
val pr_rhs : env -> evar_map -> (clause,clause) rhs -> Pp.t
val pr_clause :
  env -> evar_map -> clause -> Pp.t
val pr_clauses :
  env -> evar_map -> clause list -> Pp.t

val pr_preclause :
  env -> evar_map -> pre_clause -> Pp.t
val pr_preclauses :
  env -> evar_map -> pre_clause list -> Pp.t


val pr_user_clause :
  env -> evar_map -> pre_equation -> Pp.t

val ppclause : clause -> unit

type rec_type_item =
  | Guarded of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of int * Id.t with_loc (* for nested wf rec: number of arguments before the side-condition, name *)

type rec_type = rec_type_item option list

val is_structural : rec_type -> bool
val has_logical : rec_type -> bool
val is_rec_call : Id.t -> Constant.t -> bool
val next_ident_away : Id.t -> Id.Set.t ref -> Id.t

type equation_option = 
  | OInd
  | OEquations
  | OTactic of Libnames.qualid

type equation_user_option = equation_option * bool

val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.t

type equation_options = equation_user_option list

val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.t

type wf_rec_info =
  Constrexpr.constr_expr * Constrexpr.constr_expr option * Id.t with_loc

type program_rec_info =
  (rec_annot, wf_rec_info) by_annot

type program_info = {
  program_loc : Loc.t option;
  program_id : Id.t;
  program_orig_type : EConstr.t; (* The original type *)
  program_sort : Sorts.t; (* The sort of this type *)
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec : program_rec_info option;
  program_impls : Impargs.manual_implicits;
  program_implicits : Impargs.implicit_status list;
}

val program_type : program_info -> EConstr.t

val map_program_info : (EConstr.t -> EConstr.t) -> program_info -> program_info

val ids_of_pats : Environ.env -> evar_map -> Names.Id.t option -> Constrexpr.constr_expr list -> Id.Set.t

val pattern_of_glob_constr :
  Environ.env ->
  evar_map ->
  Names.Id.Set.t ->
  Names.Name.t ->
  Glob_term.glob_constr ->
  Names.Id.Set.t * (user_pat, [ `any] ) DAst.t


val interp_pat : Environ.env -> Evd.evar_map -> Vernacexpr.notation_declaration list -> avoid:Id.Set.t ->
  (program_info * Names.Name.t list) option ->
  Constrexpr.constr_expr -> 
  Id.Set.t * user_pats

val interp_eqn : env -> Evd.evar_map -> Vernacexpr.notation_declaration list -> program_info ->
  avoid:Id.Set.t ->
  pre_equation -> pre_clause

val wit_equations_list : pre_equation list Genarg.uniform_genarg_type

val is_recursive : Names.Id.t -> pre_equation wheres -> bool

val equations_attributes : Attributes.vernac_flags -> equation_user_option list
val derive_flags : (bool option * bool option) Attributes.attribute
val equations_tactic : Libnames.qualid option Attributes.attribute
