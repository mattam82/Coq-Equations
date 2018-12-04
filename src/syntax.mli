(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr
open Environ
open Names
open Equations_common
open Ltac_plugin

type 'a with_loc = Loc.t * 'a

(** User-level patterns *)
type generated = bool

type rec_annotation =
  | Nested
  | Mutual

type user_rec_annot = rec_annotation option

type identifier = Names.Id.t

type user_pat =
    PUVar of identifier * generated
  | PUCstr of constructor * int * user_pats
  | PUInac of Constrexpr.constr_expr
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
  | MutualOn of rec_arg
  | NestedOn of rec_arg option

type program_body =
  | ConstrExpr of Constrexpr.constr_expr
  | Constr of EConstr.constr (* We interpret a constr by substituting
                                [Var names] of the lhs bound variables
                                with the proper de Bruijn indices *)

type lhs = user_pats (* p1 ... pn *)
and ('a,'b) rhs =
    Program of program_body * 'a where_clause list
  | Empty of identifier with_loc
  | Rec of Constrexpr.constr_expr * Constrexpr.constr_expr option *
             identifier with_loc option * 'b list
  | Refine of Constrexpr.constr_expr * 'b list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) Util.union *
      'b list
and pre_prototype =
  identifier with_loc * user_rec_annot * Constrexpr.local_binder_expr list * Constrexpr.constr_expr *
  (Id.t with_loc, Constrexpr.constr_expr * Constrexpr.constr_expr option) by_annot option

and ('a, 'b) by_annot =
  | Structural of 'a
  | WellFounded of 'b

and 'a where_clause = pre_prototype * 'a list

type program = (signature * clause list) list
and signature = identifier * rel_context * constr (* f : Π Δ. τ *)
and clause = Loc.t option * lhs * (clause, clause) rhs (* lhs rhs *)

type pre_equation = Constrexpr.constr_expr input_pats * (pre_equation, pre_equation) rhs

type pre_clause = Loc.t option * lhs * (pre_equation, pre_clause) rhs

type pre_equations = pre_equation where_clause list

(* val pr_user_pat : env -> user_pat -> Pp.t *)
val pr_user_pats : env -> user_pats -> Pp.t

val pr_lhs : env -> user_pats -> Pp.t
val pplhs : user_pats -> unit
val pr_rhs : env -> (clause,clause) rhs -> Pp.t
val pr_clause :
  env -> clause -> Pp.t
val pr_clauses :
  env -> clause list -> Pp.t

val pr_preclause :
  env -> pre_clause -> Pp.t
val pr_preclauses :
  env -> pre_clause list -> Pp.t

val pr_user_clause :
  env -> pre_equation -> Pp.t

val ppclause : clause -> unit

type rec_type =
  | Guarded of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of logical_rec
and logical_rec =
  | LogicalDirect of Id.t with_loc
  | LogicalProj of rec_info
and rec_info = {
  comp_app : constr;
  comp_proj : Constant.t;
  comp_recarg : int;
}
val is_structural : rec_type option -> bool
val is_rec_call : Evd.evar_map -> logical_rec -> EConstr.constr -> bool
val next_ident_away : Id.t -> Id.Set.t ref -> Id.t

type equation_option = 
  | OInd of bool | ORec of Id.t with_loc option 
  | OComp of bool 
  | OEquations of bool

type equation_user_option = equation_option

val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.t

type equation_options = equation_option list

val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.t

type wf_rec_info =
  Constrexpr.constr_expr * Constrexpr.constr_expr option * logical_rec

type program_rec_info =
  (rec_annot, wf_rec_info) by_annot

type program_info = {
  program_loc : Loc.t;
  program_id : Id.t;
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec : program_rec_info option;
  program_impls : Impargs.manual_explicitation list;
}

val program_type : program_info -> EConstr.t

val map_program_info : (EConstr.t -> EConstr.t) -> program_info -> program_info

val ids_of_pats : Names.Id.t option -> Constrexpr.constr_expr list -> Id.Set.t

val interp_pat : Environ.env -> ?avoid:Id.Set.t ref ->
  program_info option ->
  Constrexpr.constr_expr -> user_pats

val interp_eqn : env -> program_info -> pre_equation -> pre_clause

val wit_equations_list : pre_equation list Genarg.uniform_genarg_type

val is_recursive : Names.Id.t -> pre_equations -> bool option
