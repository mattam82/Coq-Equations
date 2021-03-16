(** Generation of equations and inductive graph *)
open EConstr

type statement = constr * types option
type statements = statement list
type recursive = bool

type node_kind =
  | Regular
  | Refine
  | Where
  | Nested of recursive

val pi1 : 'a * 'b * 'c -> 'a
val pi2 : 'a * 'b * 'c -> 'b
val match_arguments : Evd.evar_map -> constr array -> constr array -> int list
val filter_arguments : int list -> 'a list -> 'a list
val is_applied_to_structarg : Names.Id.t -> Syntax.rec_type -> int -> bool option

val smash_ctx_map : Environ.env -> Evd.evar_map -> Context_map.context_map -> Context_map.context_map * EConstr.t list

val subst_protos: Names.Constant.t list -> Names.GlobRef.t -> Hints.hint_term

val find_rec_call : Syntax.rec_type ->
           Evd.evar_map ->
  (constr * (constr * int list) * (constr * int list) option * int *
   EConstr.rel_context * Constr.t)
           list ->
           Constr.constr ->
           Constr.constr list ->
           (int * Constr.t * int list *
            Constr.rel_context *
            (Constr.constr list * Constr.constr list * Constr.constr list))
           option

val abstract_rec_calls : Evd.evar_map -> Names.Id.Set.t ->
  ?do_subst:bool ->
  Syntax.rec_type ->
  int ->
  (constr * (constr * int list) * (constr * int list) option * int *
   EConstr.rel_context * Constr.t)
  list -> constr -> rel_context * int * constr
val subst_app :Evd.evar_map ->
  constr ->
  (int -> constr -> constr array -> constr) ->
  constr -> constr
val subst_comp_proj : Evd.evar_map ->
  constr -> constr -> constr -> constr
val subst_comp_proj_split : Evd.evar_map ->
  constr -> constr -> Splitting.splitting -> Splitting.splitting
val clear_ind_assums : Environ.env -> Evd.evar_map ->
  Names.MutInd.t ->
  Equations_common.rel_context -> Equations_common.rel_context
val compute_elim_type :
  Environ.env ->
  Equations_common.esigma -> Names.Id.Set.t ->
  Syntax.rec_type ->
  (constr * (constr * int list) * (constr * int list) option * int *
   EConstr.rel_context * Constr.t)
  list ->
  Names.MutInd.t ->
  int ->
         (int *
          ((EConstr.constr * int list) *
           ((EConstr.constr * int list) * Names.Id.t * Splitting.splitting)
           option * Splitting.path * EConstr.rel_context * EConstr.types *
           EConstr.constr list * (EConstr.constr * (int * int)) option * (node_kind * bool)) *
          (int *
           (bool * unit Proofview.tactic * EConstr.t * EConstr.constr option))
          list)
         list ->
  (node_kind * 'e * 'f * 'g option) list ->
  rel_context -> constr -> types -> int * types
val replace_vars_context :
  Names.Id.t list ->
  Equations_common.rel_declaration list ->
  int * Equations_common.rel_declaration list
val pr_where :
  Environ.env -> Evd.evar_map -> Constr.rel_context -> Splitting.where_clause -> Pp.t
val where_instance : Splitting.where_clause list -> constr list
val arguments : Evd.evar_map -> constr -> constr array
val unfold_constr : Evd.evar_map -> constr -> Proofview.V82.tac

(** Unfolding lemma tactic *)

type rec_subst = (Names.Id.t * (int option * EConstr.constr)) list

val cut_problem :
  Evd.evar_map -> rec_subst ->
  Equations_common.rel_declaration list ->
  Equations_common.rel_declaration list * Context_map.pat list *
  Equations_common.rel_declaration list

val map_proto : Evd.evar_map -> int option -> EConstr.t -> EConstr.t -> EConstr.t


val subst_rec :
  Environ.env -> Evd.evar_map -> Context_map.context_map ->
  rec_subst ->
  Equations_common.rel_context * Context_map.pat list *
  Equations_common.rel_context ->
  Context_map.context_map * Context_map.context_map

val subst_rec_programs :
  Environ.env ->
  Evd.evar_map ->
  Splitting.program list ->
  (EConstr.constr * Names.Id.t * Splitting.splitting) Splitting.PathMap.t *
  Splitting.program list

val unfold_programs :
  Environ.env ->
  Evd.evar_map ref ->
  Equations_common.flags ->
  Syntax.rec_type ->
  (Splitting.program * Splitting.compiled_program_info) list ->
  (Splitting.program * (Splitting.program * Splitting.compiled_program_info) option *
   Splitting.compiled_program_info * Principles_proofs.equations_info) list

type alias

val build_equations :
  bool ->
  Environ.env ->
  Evd.evar_map ->
  ?alias:alias ->
  Syntax.rec_type ->
  (Splitting.program * Splitting.program option *
   Splitting.compiled_program_info * Principles_proofs.equations_info) list ->
  unit


val all_computations :
  Environ.env ->
  Evd.evar_map ->
  ((EConstr.constr * int list) * Names.Id.t * Splitting.splitting)
    option ->
  (Splitting.program * Splitting.program option * 'b * Principles_proofs.equations_info) list ->
  (((EConstr.t * int list) *
    alias option * Splitting.path * EConstr.rel_context * EConstr.t *
    EConstr.constr list * (EConstr.constr * (int * int)) option *
    (node_kind * bool)) *
   (Equations_common.rel_context * EConstr.t *
    alias option * EConstr.constr list * EConstr.t * EConstr.t *
    (node_kind * bool) * Splitting.splitting_rhs)
     list)
    list

val computations :            Environ.env ->
           Evd.evar_map ->
  alias option ->
           node_kind * bool ->
  Splitting.program ->
           Principles_proofs.equations_info ->
           ((Equations_common.rel_context * EConstr.t *
             alias option * EConstr.constr list * EConstr.t *
             EConstr.t * (node_kind * bool) * Splitting.splitting_rhs *
             ((EConstr.t * int list) *
              alias option * Splitting.path * Equations_common.rel_context *
              EConstr.t * EConstr.constr list * (EConstr.constr * (int * int)) option *
              'c)
             list option)
            list as 'c)

val make_alias : (EConstr.t * Names.Id.t * Splitting.splitting) -> alias
