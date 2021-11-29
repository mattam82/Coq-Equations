open EConstr

type where_map = (constr * Names.Id.t * Splitting.splitting) Splitting.PathMap.t

type equations_info = {
 equations_id : Names.Id.t;
 equations_where_map : where_map;
 equations_f : EConstr.t;
 equations_prob : Context_map.context_map }

type ind_info = {
 term_info : Splitting.term_info;
 pathmap : (Names.Id.t * Constr.t list) Splitting.PathMap.t; (* path -> inductive name + parameters (de Bruijn) *)
 wheremap : where_map;
}

val find_helper_info : Environ.env -> Evd.evar_map ->
  Splitting.term_info ->
  EConstr.t -> Names.Constant.t * (int * int)
val below_transparent_state : unit -> TransparentState.t
val simpl_star : unit Proofview.tactic
val eauto_with_below :
  ?depth:Int.t -> ?strategy:Class_tactics.search_strategy -> Hints.hint_db_name list -> unit Proofview.tactic
val wf_obligations_base : Splitting.term_info -> string
val simp_eqns : Hints.hint_db_name list -> unit Proofview.tactic
val simp_eqns_in :
  Locus.clause -> Hints.hint_db_name list -> unit Proofview.tactic
val autorewrites : string -> unit Proofview.tactic
val autorewrite_one : string -> unit Proofview.tactic

(** The multigoal fix tactic *)
val mutual_fix : string list -> int list -> unit Proofview.tactic

val find_helper_arg :
  Environ.env -> Evd.evar_map ->
  Splitting.term_info -> EConstr.t -> 'a array -> Names.Constant.t * int * 'a
val find_splitting_var : Evd.evar_map ->
  Context_map.pat list -> int -> constr list -> Names.Id.t
val intros_reducing : unit -> unit Proofview.tactic
val cstrtac : unit Proofview.tactic
val destSplit : Splitting.splitting -> Splitting.splitting option array option
val destRefined : Splitting.splitting -> Splitting.splitting option
val destWheres : Splitting.splitting -> (Context_map.context_map * Splitting.where_clause list) option
val map_opt_split : ('a -> 'b option) -> 'a option -> 'b option
val solve_ind_rec_tac : Splitting.term_info -> unit Proofview.tactic

val gather_subst :            'a ->
           Evd.evar_map ->
           EConstr.t -> EConstr.t list -> int -> EConstr.t list

val aux_ind_fun :
  ind_info ->
  int * int ->
  (Names.Id.t * EConstr.types * Splitting.program) list ->
  Splitting.program option ->
  Names.Id.t list -> Splitting.program -> unit Proofview.tactic
val ind_fun_tac :
  Syntax.rec_type ->
  Constr.t ->
  ind_info ->
  Names.Id.t ->
  (Names.Id.t * EConstr.types * Splitting.program) list ->
  (Splitting.program * Splitting.program option * Splitting.compiled_program_info * 'b) list ->
  unit Proofview.tactic

val prove_unfolding_lemma :
  Splitting.term_info ->
  where_map ->
  Names.Constant.t ->
  Names.Constant.t ->
  Splitting.program -> Splitting.program ->
  unit Proofview.tactic
  
val ind_elim_tac :
  constr ->
  int -> int ->
  Splitting.term_info ->
  Names.GlobRef.t ->
  unit Proofview.tactic
