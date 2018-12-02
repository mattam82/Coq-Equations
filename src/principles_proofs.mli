open EConstr

module PathOT :
  sig
    type t = Covering.path
    val compare : t -> t -> int
  end
module PathMap : CSig.MapS with type key = PathOT.t

type where_map = (constr * Names.Id.t * Covering.splitting) Evar.Map.t

type equations_info = {
 equations_id : Names.Id.t;
 equations_where_map : where_map;
 equations_f : Constr.t;
 equations_prob : Covering.context_map;
 equations_split : Covering.splitting }

type ind_info = {
 term_info : Splitting.term_info;
 pathmap : (Names.Id.t * Constr.t list) PathMap.t; (* path -> inductive name + parameters (de Bruijn) *)
 wheremap : where_map;
}

val find_helper_info :
  Splitting.term_info ->
  Constr.t -> Evar.t * int * Names.Id.t
val below_transparent_state : unit -> TransparentState.t
val simpl_star : Proofview.V82.tac
val eauto_with_below :
  ?depth:Int.t -> Hints.hint_db_name list -> Proofview.V82.tac
val wf_obligations_base : Splitting.term_info -> string
val simp_eqns : Hints.hint_db_name list -> Proofview.V82.tac
val simp_eqns_in :
  Locus.clause -> Hints.hint_db_name list -> Proofview.V82.tac
val autorewrites : string -> Proofview.V82.tac
val autorewrite_one : string -> Proofview.V82.tac

(** The multigoal fix tactic *)
val mutual_fix : string list -> int list -> unit Proofview.tactic

val find_helper_arg :
  Splitting.term_info -> Constr.t -> 'a array -> Evar.t * int * 'a
val find_splitting_var : Evd.evar_map ->
  Covering.pat list -> int -> constr list -> Names.Id.t
val intros_reducing : Proofview.V82.tac
val cstrtac : 'a -> Proofview.V82.tac
val destSplit : Covering.splitting -> Covering.splitting option array option
val destRefined : Covering.splitting -> Covering.splitting option
val destWheres : Covering.splitting -> Covering.where_clause list option
val map_opt_split : ('a -> 'b option) -> 'a option -> 'b option
val solve_ind_rec_tac : Splitting.term_info -> unit Proofview.tactic
val aux_ind_fun :
  ind_info ->
  int * int ->
  Covering.splitting option ->
  Names.Id.t list -> Covering.splitting -> Proofview.V82.tac
val ind_fun_tac :
  Syntax.rec_type option ->
  Constr.t ->
  ind_info ->
  Names.Id.t ->
  Covering.splitting -> Covering.splitting option ->
  (Syntax.program_info * Splitting.compiled_program_info * equations_info) list ->
  unit Proofview.tactic

val prove_unfolding_lemma :
  Splitting.term_info ->
  where_map ->
  Syntax.logical_rec ->
  Names.Constant.t ->
  Names.Constant.t ->
  Covering.splitting -> Covering.splitting ->
  Goal.goal Evd.sigma ->
  Goal.goal list Evd.sigma
  
val ind_elim_tac :
  constr ->
  int -> int ->
  Splitting.term_info ->
  Names.GlobRef.t ->
  unit Proofview.tactic
