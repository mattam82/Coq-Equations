(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

val debug : bool
val new_untyped_evar : unit -> Evd.evar
val check_term :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.types -> unit
val check_type : Environ.env -> Evd.evar_map -> Term.types -> unit
val abstract_undefined : Evd.evar_map -> Evd.evar_map
val typecheck_rel_context :
  Evd.evar_map ->
  (Names.Name.t * Term.constr option * Term.types) list -> unit
val below_tactics_path : Names.dir_path
val below_tac : string -> Names.kernel_name
val tacident_arg :
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : 'c; name : 'd; pattern : 'e;
    reference : Libnames.reference; tacexpr : 'f; term : 'g; utrm : 'h >
  Tacexpr.gen_tactic_arg
val tacvar_arg :
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : Genarg.rlevel; name : 'c;
    pattern : 'd; reference : 'e; tacexpr : 'f; term : 'g; utrm : 'h >
  Tacexpr.gen_tactic_arg
val rec_tac :
  Names.Id.t ->
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : Genarg.rlevel; name : 'c;
    pattern : 'd; reference : Libnames.reference; tacexpr : 'e; term : 'f;
    utrm : 'g >
  Tacexpr.gen_tactic_expr
val rec_wf_tac :
  Names.Id.t ->
  Names.Id.t ->
  'a ->
  < constant : 'b; dterm : 'c; level : Genarg.rlevel; name : 'd;
    pattern : 'e; reference : Libnames.reference; tacexpr : 'f; term : 'a;
    utrm : 'g >
  Tacexpr.gen_tactic_expr
val unfold_recursor_tac : unit -> unit Proofview.tactic
val equations_tac_expr :
  unit ->
  < constant : 'a; dterm : 'b; level : 'c; name : 'd; pattern : 'e;
    reference : Libnames.reference; tacexpr : 'f; term : 'g; utrm : 'h >
  Tacexpr.gen_tactic_expr
val equations_tac : unit -> unit Proofview.tactic
val set_eos_tac : unit -> unit Proofview.tactic
val solve_rec_tac : unit -> unit Proofview.tactic
val find_empty_tac : unit -> unit Proofview.tactic
val pi_tac : unit -> unit Proofview.tactic
val noconf_tac : unit -> unit Proofview.tactic
val simpl_equations_tac : unit -> unit Proofview.tactic
val reference_of_global : Globnames.global_reference -> Libnames.reference
val solve_equation_tac :
  'a ->
  Tacexpr.r_dispatch Tacexpr.gen_tactic_arg list -> unit Proofview.tactic
val impossible_call_tac :
  Globnames.global_reference -> Tacexpr.glob_tactic_expr
val depelim_tac : Names.Id.t -> unit Proofview.tactic
val do_empty_tac : Names.Id.t -> unit Proofview.tactic
val depelim_nosimpl_tac : Names.Id.t -> unit Proofview.tactic
val simpl_dep_elim_tac : unit -> unit Proofview.tactic
val depind_tac : Names.Id.t -> unit Proofview.tactic
val mkNot : Term.constr -> Term.constr
val mkProd_or_subst :
  Names.Name.t * Constr.constr option * Term.types ->
  Term.types -> Term.types
val mkProd_or_clear : Context.rel_declaration -> Term.constr -> Constr.constr
val it_mkProd_or_clear :
  Term.constr -> Context.rel_declaration list -> Term.constr
val mkLambda_or_subst :
  Names.Name.t * Constr.constr option * Term.types ->
  Term.constr -> Term.constr
val mkLambda_or_subst_or_clear :
  Names.Name.t * Constr.constr option * Term.types ->
  Term.constr -> Term.constr
val mkProd_or_subst_or_clear :
  Names.Name.t * Constr.constr option * Term.types ->
  Term.constr -> Term.types
val it_mkProd_or_subst :
  Term.types -> Context.rel_declaration list -> Term.constr
val it_mkProd_or_clean :
  Constr.constr ->
  (Names.name * Constr.t option * Constr.t) list -> Term.constr
val it_mkLambda_or_subst :
  Term.constr -> Context.rel_declaration list -> Term.constr
val it_mkLambda_or_subst_or_clear :
  Term.constr ->
  (Names.Name.t * Constr.constr option * Term.types) list -> Term.constr
val it_mkProd_or_subst_or_clear :
  Term.constr ->
  (Names.Name.t * Constr.constr option * Term.types) list -> Term.constr
type pat =
    PRel of int
  | PCstr of Term.pconstructor * pat list
  | PInac of Term.constr
  | PHide of int
type user_pat =
    PUVar of Names.identifier
  | PUCstr of Names.constructor * int * user_pat list
  | PUInac of Constrexpr.constr_expr
type user_pats = user_pat list
type context_map = Context.rel_context * pat list * Context.rel_context
val mkInac : Environ.env -> Term.constr -> Term.constr
val mkHide : Environ.env -> Term.constr -> Term.constr
val pat_constr : pat -> Term.constr
val constr_of_pat : ?inacc:bool -> Environ.env -> pat -> Term.constr
val constrs_of_pats :
  ?inacc:bool -> Environ.env -> pat list -> Term.constr list
val pat_vars : pat -> Int.Set.t
val pats_vars : pat list -> Int.Set.t
val inaccs_of_constrs : Term.constr list -> pat list
val pats_of_constrs : Term.constr list -> pat list
val pat_of_constr : Term.constr -> pat
val pr_constr_pat : Environ.env -> Term.constr -> Pp.std_ppcmds
val pr_pat : Environ.env -> pat -> Pp.std_ppcmds
val pr_context : Environ.env -> Context.rel_declaration list -> Pp.std_ppcmds
val ppcontext : Context.rel_declaration list -> unit
val pr_context_map :
  Environ.env ->
  Context.rel_context * pat list * Context.rel_declaration list ->
  Pp.std_ppcmds
val ppcontext_map :
  Context.rel_context * pat list * Context.rel_declaration list -> unit
val typecheck_map :
  Evd.evar_map ->
  Context.rel_context * pat list *
  (Names.Name.t * Term.constr option * Constr.constr) list -> unit
val check_ctx_map :
  Evd.evar_map ->
  Context.rel_context * pat list * Context.rel_declaration list ->
  Context.rel_context * pat list * Context.rel_declaration list
val mk_ctx_map :
  Evd.evar_map ->
  Context.rel_context ->
  pat list ->
  Context.rel_declaration list ->
  Context.rel_context * pat list * Context.rel_declaration list
val subst_pats_constr : int -> pat list -> Term.constr -> Term.constr
val subst_context :
  pat list ->
  ('a * Term.constr option * Term.constr) list ->
  ('a * Term.constr option * Term.constr) list
val specialize : pat list -> pat -> pat
val specialize_constr : pat list -> Term.constr -> Term.constr
val specialize_pats : pat list -> pat list -> pat list
val specialize_rel_context :
  pat list -> Context.rel_declaration list -> Context.rel_declaration list
val mapping_constr : context_map -> Term.constr -> Term.constr
val subst_constr_pat : int -> Term.constr -> pat -> pat
val subst_constr_pats : int -> Term.constr -> pat list -> pat list
val subst_rel_context :
  int ->
  Constr.constr ->
  ('a * Constr.constr option * Constr.constr) list ->
  ('a * Constr.constr option * Constr.constr) list
val subst_telescope :
  Constr.constr ->
  ('a * Constr.constr option * Constr.constr) list ->
  ('a * Constr.constr option * Constr.constr) list
val subst_in_ctx :
  int -> Term.constr -> Context.rel_context -> Context.rel_context
val set_in_ctx :
  int -> Term.constr -> Context.rel_context -> Context.rel_context
val lift_patn : int -> int -> pat -> pat
val lift_patns : int -> int -> pat list -> pat list
val lift_pat : int -> pat -> pat
val lift_pats : int -> pat list -> pat list
type program = signature * clause list
and signature = Names.identifier * Context.rel_context * Term.constr
and clause = lhs * clause rhs
and lhs = user_pats
and 'a rhs =
    Program of Constrexpr.constr_expr
  | Empty of Names.identifier Loc.located
  | Rec of Names.identifier Loc.located * Constrexpr.constr_expr option *
      'a list
  | Refine of Constrexpr.constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) Util.union *
      'a list
type path = Evd.evar list
type splitting =
    Compute of context_map * Term.types * splitting_rhs
  | Split of context_map * int * Term.types * splitting option array
  | Valid of context_map * Term.types * Names.identifier list *
      Tacmach.tactic * (Proofview.entry * Proofview.proofview) *
      (Proof_type.goal * Term.constr list * context_map * splitting) list
  | RecValid of Names.identifier * splitting
  | Refined of context_map * refined_node * splitting
and refined_node = {
  refined_obj : Names.identifier * Term.constr * Term.types;
  refined_rettyp : Term.types;
  refined_arg : int;
  refined_path : path;
  refined_ex : Term.existential_key;
  refined_app : Term.constr * Term.constr list;
  refined_revctx : context_map;
  refined_newprob : context_map;
  refined_newprob_to_lhs : context_map;
  refined_newty : Term.types;
}
and splitting_rhs = RProgram of Term.constr | REmpty of int
and unification_result = (context_map * int * Term.constr * pat) option
type problem = Names.identifier * lhs
val specialize_mapping_constr : context_map -> Term.constr -> Term.constr
val rels_of_tele : 'a list -> Term.constr list
val patvars_of_tele : 'a list -> pat list
val pat_vars_list : int -> pat list
val intset_of_list : Int.Set.elt list -> Int.Set.t
val split_context : int -> 'a list -> 'a list * 'a * 'a list
val split_tele :
  int ->
  Context.rel_context ->
  Context.rel_declaration list * Context.rel_declaration *
  Context.rel_declaration list
val rels_above : 'a list -> int -> Int.Set.t
val is_fix_proto : Term.constr -> bool
val fix_rels : ('a * 'b * Term.constr) list -> Int.Set.t
val dependencies_of_rel :
  ('a * Constr.constr option * Constr.constr) list ->
  Int.Set.elt -> Int.Set.t
val dependencies_of_term :
  ('a * Constr.constr option * Constr.constr) list ->
  Constr.constr -> Int.Set.t
val non_dependent :
  ('a * 'b * Term.constr) list -> Constr.constr -> Int.Set.t
val subst_term_in_context :
  Term.constr -> ('a * 'b * Term.constr) list -> ('a * 'b * Term.constr) list
val strengthen :
  ?full:bool ->
  ?abstract:bool ->
  Context.rel_context ->
  Int.Set.elt ->
  Term.constr ->
  (Context.rel_declaration list * pat list * Context.rel_context) *
  (int * int) list
val id_subst : 'a list -> 'a list * pat list * 'a list
val eq_context_nolet :
  Environ.env ->
  Evd.evar_map -> Context.rel_context -> Context.rel_context -> bool
val check_eq_context_nolet :
  Environ.env ->
  Evd.evar_map ->
  Context.rel_context * pat list * Context.rel_context ->
  Context.rel_context * pat list * Context.rel_declaration list -> unit
val compose_subst :
  ?sigma:Evd.evar_map ->
  Context.rel_context * pat list * Context.rel_context ->
  Context.rel_context * pat list * Context.rel_declaration list ->
  Context.rel_context * pat list * Context.rel_declaration list
val push_mapping_context :
  'a * Term.constr option * Term.constr ->
  ('a * Term.constr option * Term.constr) list * pat list *
  ('a * Term.constr option * Term.constr) list ->
  ('a * Term.constr option * Term.constr) list * pat list *
  ('a * Term.constr option * Term.constr) list
val lift_subst :
  Evd.evar_map -> context_map -> Context.rel_context -> context_map
val single_subst :
  Evd.evar_map ->
  Int.Set.elt ->
  pat ->
  Context.rel_context -> Context.rel_context * pat list * Context.rel_context
exception Conflict
exception Stuck
type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
val unify :
  Evd.evar_map ->
  Int.Set.t ->
  Context.rel_context ->
  Term.constr ->
  Term.constr -> Context.rel_context * pat list * Context.rel_context
val unify_constrs :
  Evd.evar_map ->
  Int.Set.t ->
  Context.rel_context ->
  Term.constr list ->
  Term.constr list -> Context.rel_context * pat list * Context.rel_context
val flexible : pat list -> 'a list -> Int.Set.t
val accessible : pat -> Int.Set.t
val accessibles : pat list -> Int.Set.t
val hidden : pat -> bool
val match_pattern : user_pat -> pat -> (Names.identifier * pat) list
val match_patterns :
  user_pat list -> pat list -> (Names.identifier * pat) list
val matches :
  user_pats -> context_map -> (Names.identifier * pat) list unif_result
val match_user_pattern :
  pat -> user_pat -> (int * user_pat) list * (Names.identifier * pat) list
val match_user_patterns :
  pat list ->
  user_pat list -> (int * user_pat) list * (Names.identifier * pat) list
val matches_user :
  context_map ->
  user_pats ->
  ((int * user_pat) list * (Names.identifier * pat) list) unif_result
val lets_of_ctx :
  Environ.env ->
  Context.rel_context ->
  Evd.evar_map ref ->
  (Names.Id.t * pat) list ->
  Term.constr list *
  (Names.name * Constr.constr option * Constr.constr) list *
  (Names.name * Constr.t option * Constr.t) list
val interp_constr_in_rhs :
  Environ.env ->
  Context.rel_context ->
  Evd.evar_map ref ->
  'a * 'b * Constrintern.internalization_env ->
  Constr.constr option ->
  (Names.Id.t * pat) list ->
  Context.rel_declaration list ->
  Constrexpr.constr_expr -> Term.constr * Term.types
val unify_type :
  Evd.evar_map ref ->
  Context.rel_context ->
  'a ->
  Term.types ->
  Context.rel_context ->
  (Term.constr *
   ((Context.rel_context * pat list * Context.rel_context) * int *
    Term.constr * pat)
   unif_result array)
  option
val blockers : user_pat list -> context_map -> int list
val pr_user_pat : Environ.env -> user_pat -> Pp.std_ppcmds
val pr_user_pats : Environ.env -> user_pat list -> Pp.std_ppcmds
val pr_lhs : Environ.env -> user_pat list -> Pp.std_ppcmds
val pplhs : user_pat list -> unit
val pr_rhs : Environ.env -> ((user_pat list * 'a) rhs as 'a) -> Pp.std_ppcmds
val pr_clause :
  Environ.env -> (user_pat list * 'a rhs as 'a) -> Pp.std_ppcmds
val pr_clauses :
  Environ.env -> (user_pat list * 'a rhs as 'a) list -> Pp.std_ppcmds
val ppclause : (user_pat list * 'a rhs as 'a) -> unit
val pr_rel_name : Context.rel_context -> int -> Pp.std_ppcmds
val pr_splitting : Environ.env -> splitting -> Pp.std_ppcmds
val ppsplit : splitting -> unit
val subst_matches_constr :
  int -> (int * Constr.constr) list -> Term.constr -> Term.constr
val is_all_variables : 'a * pat list * 'b -> bool
val do_renamings : (Names.name * 'a * 'b) list -> (Names.name * 'a * 'b) list
val split_var :
  'a * Evd.evar_map ref ->
  int ->
  Context.rel_context ->
  (int * (Names.name * Constr.t option * Constr.t) list *
   context_map option array)
  option
val find_empty : 'a * Evd.evar_map ref -> Context.rel_context -> int option
val rel_of_named_context :
  (Names.Id.t * Constr.constr option * Constr.constr) list ->
  (Names.name * Constr.constr option * Constr.constr) list * Names.Id.t list
val variables_of_pats : pat list -> (int * bool) list
val pats_of_variables : (int * bool) list -> pat list
val lift_rel_declaration :
  int ->
  'a * Constr.constr option * Constr.constr ->
  'a * Constr.constr option * Constr.constr
val named_of_rel_context :
  (Names.name * Constr.constr option * Constr.constr) list ->
  Constr.constr list *
  (Names.Id.t * Constr.constr option * Constr.constr) list
val lookup_named_i :
  Names.Id.t -> (Names.Id.t * 'a * 'b) list -> int * (Names.Id.t * 'a * 'b)
val instance_of_pats :
  'a ->
  'b ->
  Context.rel_context ->
  (int * bool) list ->
  (Names.name * Constr.constr option * Constr.constr) list * pat list *
  pat list
val push_rel_context_eos : Context.rel_context -> Environ.env -> Environ.env
val split_at_eos :
  ('a * 'b * Term.constr) list ->
  ('a * 'b * Term.constr) list * ('a * 'b * Term.constr) list
val pr_problem :
  Names.Id.t * 'a * 'b ->
  Environ.env -> Context.rel_context * pat list * 'c -> Pp.std_ppcmds
val rel_id : (Names.Name.t * 'a * 'b) list -> int -> Names.Id.t
val push_named_context :
  Context.named_declaration list -> Environ.env -> Environ.env
val covering_aux :
  Environ.env ->
  Evd.evar_map ref ->
  Names.identifier * bool * Constrintern.internalization_env ->
  ((user_pats * 'a rhs as 'a) * bool) list ->
  ('a * bool) list ->
  Evd.evar list ->
  Context.rel_context * pat list * Context.rel_context ->
  Context.rel_context -> Constr.constr -> splitting option
val covering :
  Environ.env ->
  Evd.evar_map ref ->
  Names.identifier * bool * Constrintern.internalization_env ->
  clause list ->
  Context.rel_context * pat list * Context.rel_context ->
  Constr.constr -> splitting
val helper_evar :
  Evd.evar_map ->
  Evd.evar ->
  Environ.env ->
  Term.types -> Loc.t * Evar_kinds.t -> Evd.evar_map * Term.constr
val gen_constant : string list -> string -> Term.constr
val coq_zero : Term.constr lazy_t
val coq_succ : Term.constr lazy_t
val coq_nat : Term.constr lazy_t
val coq_nat_of_int : int -> Term.constr
val term_of_tree :
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  Environ.env ->
  'a * 'b * 'c ->
  'd ->
  splitting ->
  (Term.existential_key * int) list * Evar.Set.t * Term.constr * Term.constr
type 'a located = 'a Loc.located
type pat_expr =
    PEApp of Libnames.reference Misctypes.or_by_notation located *
      pat_expr located list
  | PEWildcard
  | PEInac of Constrexpr.constr_expr
  | PEPat of Constrexpr.cases_pattern_expr
type user_pat_expr = pat_expr located
type user_pat_exprs = user_pat_expr located
type input_pats =
    SignPats of user_pat_expr list
  | RefinePats of user_pat_expr list
type pre_equation =
    Names.identifier located option * input_pats * pre_equation rhs
val next_ident_away : Names.Id.t -> Names.Id.t list ref -> Names.Id.t
type rec_type = Structural | Logical of rec_info
and rec_info = {
  comp : Names.constant;
  comp_app : Term.constr;
  comp_proj : Names.constant;
  comp_recarg : int;
}
val lift_constrs : int -> Constr.constr list -> Constr.constr list
val array_remove_last : 'a array -> 'a array
val array_chop_last : 'a array -> 'a array * 'a array
val abstract_rec_calls :
  ?do_subst:bool ->
  rec_type option ->
  int ->
  (Term.constr * Term.constr option * int * Term.constr) list ->
  Term.constr -> Context.rel_context * int * Constr.constr
val below_transparent_state : unit -> Names.transparent_state
val simpl_star : Proof_type.tactic
val eauto_with_below : Hints.hint_db_name list -> Tacmach.tactic
val simp_eqns : Hints.hint_db_name list -> Proof_type.tactic
val simp_eqns_in :
  Locus.clause -> Hints.hint_db_name list -> Proof_type.tactic
val autorewrites : string -> Proof_type.tactic
val autorewrite_one : string -> Proofview.V82.tac
type term_info = {
  base_id : string;
  polymorphic : bool;
  helpers_info : (Term.existential_key * int * Names.identifier) list;
}
val find_helper_info :
  term_info -> Term.constr -> Term.existential_key * int * Names.identifier
val find_helper_arg :
  term_info -> Term.constr -> 'a array -> Term.existential_key * 'a
val find_splitting_var : pat list -> int -> Term.constr list -> Names.Id.t
val intros_reducing : Proof_type.tactic
val to82 : 'a Proofview.tactic -> Proofview.V82.tac
val of82 : Proofview.V82.tac -> unit Proofview.tactic
val aux_ind_fun : term_info -> splitting -> Proof_type.tactic
val is_structural : rec_type option -> bool
val ind_fun_tac :
  rec_type option ->
  Term.constr ->
  term_info -> Names.Id.t -> splitting -> 'a -> Proof_type.tactic
val mapping_rhs : context_map -> splitting_rhs -> splitting_rhs
val map_rhs :
  (Term.constr -> Term.constr) ->
  (int -> int) -> splitting_rhs -> splitting_rhs
val clean_clause :
  'a * 'b * 'c * splitting_rhs -> 'a * 'b * 'c * splitting_rhs
val map_evars_in_constr :
  ((Names.Id.t -> Term.constr) -> 'a -> 'b) -> 'a -> 'b
val map_ctx_map :
  (Constr.t -> Constr.t) ->
  Context.rel_context * 'a * Context.rel_context ->
  Context.rel_context * 'a * Context.rel_context
val map_split : (Term.constr -> Term.constr) -> splitting -> splitting
val map_evars_in_split :
  ((Names.Id.t -> Term.constr) -> Term.constr -> Term.constr) ->
  splitting -> splitting
val ( &&& ) : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
val array_filter_map : ('a -> 'b option) -> 'a array -> 'b array
val subst_rec_split :
  bool ->
  Term.constr ->
  Context.rel_context * pat list * Context.rel_context ->
  (Names.Id.t * Constr.constr) list -> splitting -> splitting
type statement = Term.constr * Term.types option
type statements = statement list
val subst_app :
  Term.constr ->
  (int -> Term.constr -> Term.constr array -> Term.constr) ->
  Term.constr -> Term.constr
val subst_comp_proj :
  Term.constr -> Term.constr -> Term.constr -> Term.constr
val subst_comp_proj_split :
  Term.constr -> Term.constr -> splitting -> splitting
val reference_of_id : Names.Id.t -> Libnames.reference
val clear_ind_assums :
  Names.mutual_inductive -> Context.rel_context -> Context.rel_context
val unfold : Names.evaluable_global_reference -> Proof_type.tactic
val ind_elim_tac :
  Term.constr ->
  'a ->
  term_info -> Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma
val pr_path : Evd.evar_map -> Evd.evar list -> Pp.std_ppcmds
val eq_path : Evar.t list -> Evar.t list -> bool
val build_equations :
  bool ->
  Environ.env ->
  Names.Id.t ->
  term_info ->
  'a ->
  Context.rel_context ->
  rec_type option ->
  Term.types ->
  Names.constant ->
  Term.constr ->
  ?alias:Term.constr * Term.constr * splitting ->
  context_map -> splitting -> unit
val rev_assoc : ('a -> 'b -> bool) -> 'a -> ('c * 'b) list -> 'c
type equation_option = OInd | ORec | OComp | OEquations
val is_comp_obl : rec_info option -> Evar_kinds.t -> bool
val hintdb_set_transparency :
  Names.Constant.t -> bool -> Hints.hint_db_name -> unit
val define_tree :
  rec_type option ->
  (Constrexpr.explicitation * (bool * bool * bool)) list ->
  Evar_kinds.obligation_definition_status ->
  Evd.evar_map ref ->
  Environ.env ->
  Names.Id.t * 'a * 'b ->
  rec_info option ->
  'c ->
  splitting ->
  (((Names.Id.t -> Term.constr) -> Term.constr -> Term.constr) ->
   (Term.existential_key * int * Names.Id.t) list ->
   Decl_kinds.locality -> Globnames.global_reference -> unit) ->
  unit
val conv_proj_call :
  Term.constr -> Names.constant -> Term.constr -> Term.constr
val convert_projection :
  Term.constr ->
  Names.constant ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
val unfold_constr : Term.constr -> Proof_type.tactic
val simpl_except : Names.Idset.t * Names.Cset.t -> Closure.RedFlags.reds
val simpl_of : Names.constant list -> (unit -> unit) * (unit -> unit)
val prove_unfolding_lemma :
  term_info ->
  Term.constr ->
  Names.constant ->
  Names.constant ->
  splitting -> Proof_type.goal Evd.sigma -> Proof_type.goal list Evd.sigma
val update_split :
  rec_type option ->
  ((Names.Id.t -> Term.constr) -> Term.constr -> Term.constr) ->
  Term.constr ->
  Context.rel_context * pat list * Context.rel_context ->
  Names.Id.t -> splitting -> splitting
val translate_cases_pattern :
  'a -> Names.Id.t list ref -> Glob_term.cases_pattern -> user_pat
val pr_smart_global :
  Libnames.reference Misctypes.or_by_notation -> Pp.std_ppcmds
val string_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> string
val ident_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> Names.identifier
val ids_of_pats : pat_expr located list -> Names.identifier list
val interp_eqn :
  Names.identifier ->
  rec_type option ->
  'a ->
  Environ.env ->
  'b ->
  'c ->
  'd ->
  'e ->
  ((Loc.t * Names.identifier) option * input_pats * 'f rhs as 'f) ->
  (user_pat list * 'g rhs as 'g)
val make_ref : string list -> string -> Globnames.global_reference
val fix_proto_ref : unit -> Names.constant
val constr_of_global : Globnames.global_reference -> Term.constr
val define_by_eqs :
  (equation_option * bool) list ->
  Names.identifier ->
  Constrexpr.local_binder list * 'a ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * Names.identifier) option * input_pats * 'b rhs as 'b) list ->
  unit
module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic
type binders_let2_argtype =
    (Constrexpr.local_binder list *
     (Names.identifier located option * Constrexpr.recursion_order_expr))
    Genarg.uniform_genarg_type
val wit_binders_let2 : binders_let2_argtype
val pr_raw_binders_let2 : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val pr_glob_binders_let2 : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val pr_binders_let2 : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val binders_let2 :
  (Constrexpr.local_binder list *
   (Names.identifier located option * Constrexpr.recursion_order_expr))
  Gram.entry
type deppat_equations_argtype = pre_equation list Genarg.uniform_genarg_type
val wit_deppat_equations : deppat_equations_argtype
val pr_raw_deppat_equations : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val pr_glob_deppat_equations : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val pr_deppat_equations : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val deppat_equations : pre_equation list Gram.entry
type equation_user_option = equation_option * bool
val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val wit_equation_user_option :
  (equation_option * bool, equation_option * bool, equation_option * bool)
  Genarg.genarg_type
val equation_user_option : (equation_option * bool) Pcoq.Gram.entry
type equation_options = (equation_option * bool) list
val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds
val wit_equation_options :
  ((equation_option * bool) list, (equation_option * bool) list,
   (equation_option * bool) list)
  Genarg.genarg_type
val equation_options : (equation_option * bool) list Pcoq.Gram.entry
val with_rollback : ('a -> 'b) -> 'a -> 'b
val equations :
  (equation_option * bool) list ->
  Loc.t * Names.identifier ->
  Constrexpr.local_binder list * 'a ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * Names.identifier) option * input_pats * 'b rhs as 'b) list ->
  unit
val int_of_coq_nat : Term.constr -> int
val gclause_none : 'a Locus.clause_expr
val solve_equations_goal :
  Proof_type.tactic ->
  Proof_type.tactic ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
val db_of_constr : Term.constr -> string
val dbs_of_constrs : Term.constr list -> string list
val depcase :
  Names.MutInd.t * int ->
  Context.rel_context * Term.constr * Globnames.global_reference
val derive_dep_elimination :
  Evd.evar_universe_context -> Names.inductive * 'a -> 'b -> Term.constr
val mkcase :
  Environ.env ->
  Term.constr ->
  Term.constr ->
  ((Names.MutInd.t * int) * Univ.universe_instance ->
   int ->
   Names.Id.t -> int -> Context.rel_context -> Term.types -> Term.constr) ->
  Term.constr
val mk_eqs :
  Environ.env ->
  Evd.evar_map ref ->
  Term.constr list -> Term.constr list -> Constr.constr -> Term.types
val derive_no_confusion :
  Environ.env -> Evd.evar_map -> Names.inductive * 'a -> unit
val pattern_call :
  ?pattern_term:bool ->
  Term.constr -> Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma
val dependencies :
  Environ.env ->
  Term.constr -> Context.named_context -> Names.Id.Set.t * Names.Idset.t
