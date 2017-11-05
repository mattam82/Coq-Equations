(** Generation of equations and inductive graph *)

type statement = Term.constr * Term.types option
type statements = statement list
type recursive = bool

type node_kind =
  | Regular
  | Refine
  | Where
  | Nested of recursive

val pi1 : 'a * 'b * 'c -> 'a
val pi2 : 'a * 'b * 'c -> 'b
val match_arguments : Term.constr array -> Term.constr array -> int list
val filter_arguments : int list -> 'a list -> 'a list
val clean_rec_calls :
  Context.Rel.Declaration.t list * int * Constr.constr ->
  Context.Rel.Declaration.t list * int * Constr.constr
val head : Term.constr -> Term.constr
val abstract_rec_calls :
  ?do_subst:bool ->
  Syntax.rec_type option ->
  int ->
  ((Term.constr * int list) * (Term.constr * int list) option * int *
   Term.constr)
  list -> Term.constr -> Context.Rel.Declaration.t list * int * Constr.constr
val subst_app :
  Term.constr ->
  (int -> Term.constr -> Term.constr array -> Term.constr) ->
  Term.constr -> Term.constr
val subst_comp_proj :
  Term.constr -> Term.constr -> Term.constr -> Term.constr
val subst_comp_proj_split :
  Term.constr -> Term.constr -> Covering.splitting -> Covering.splitting
val reference_of_id : Names.Id.t -> Libnames.reference
val clear_ind_assums :
  Names.mutual_inductive ->
  Equations_common.rel_context -> Equations_common.rel_context
val type_of_rel : Term.constr -> Equations_common.rel_context -> Constr.t
val compute_elim_type :
  Environ.env ->
  Equations_common.esigma ->
  Syntax.rec_type option ->
  ((Constr.t * int list) * (Constr.t * int list) option * int *
   Term.constr)
  list ->
  Names.mutual_inductive ->
  int ->
         (int *
          ((Constr.constr * int list) *
           ((Constr.constr * int list) * Names.Id.t * Covering.splitting)
           option * Covering.path * Equations_common.rel_context * Constr.types *
           Constr.constr list * (Constr.constr * int) list * (node_kind * bool)) *
          (int *
           (bool * unit Proofview.tactic * Constr.t * Constr.constr option))
          list)
         list ->
  (node_kind * 'e * 'f * 'g) list ->
  Equations_common.rel_context -> Constr.t -> Constr.types -> int * Constr.types

val replace_vars_context :
  Names.Id.t list ->
  Equations_common.rel_declaration list ->
  int * Equations_common.rel_declaration list
val pr_where :
  Environ.env -> Context.Rel.t -> Covering.where_clause -> Pp.std_ppcmds
val where_instance : Covering.where_clause list -> Term.constr list
val arguments : Term.constr -> Term.constr array
val unfold_constr : Term.constr -> Proofview.V82.tac

(** Unfolding lemma tactic *)

val subst_rec_split :            Environ.env ->
           Evd.evar_map ->
           Term.constr ->
           bool ->
           int option ->
           Covering.context_map ->
           (Names.Id.t * Term.constr) list ->
           Covering.splitting -> Covering.splitting

  
val update_split : Environ.env ->
  Evd.evar_map ref ->
  Syntax.rec_type option ->
  ((Names.Id.t -> Constr.constr) -> Constr.constr -> Constr.constr) ->
  Constr.constr ->
  Covering.context_map ->
  (Names.Id.t * Constr.constr) list -> Covering.splitting -> Covering.splitting * Principles_proofs.where_map

val build_equations :
  bool ->
  Environ.env ->
  Evd.evar_map ->
  ?alias:Constr.t * Names.Id.t * Covering.splitting ->
  (Splitting.program_info * Splitting.compiled_program_info * Principles_proofs.equations_info) list ->
  unit
