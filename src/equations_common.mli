val __coq_plugin_name : string
val ( $ ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val proper_tails : 'a list -> 'a list list
val list_tabulate : (int -> 'a) -> int -> 'a list
val list_map_filter_i : (int -> 'a -> 'b option) -> 'a list -> 'b list
val list_try_find : ('a -> 'b) -> 'a list -> 'b
val list_try_find_i : (int -> 'a -> 'b option) -> int -> 'a list -> 'b option
val find_constant : Coqlib.message -> string list -> string -> Term.constr
val contrib_name : string
val init_constant : string list -> string -> Term.constr
val init_reference : string list -> string -> Globnames.global_reference
val make_definition :
  ?opaque:'a ->
  ?poly:Decl_kinds.polymorphic ->
  Evd.evar_map ref ->
  ?types:Term.constr -> Term.constr -> Entries.definition_entry
val declare_constant :
  Names.identifier ->
  Term.constr ->
  Term.constr option ->
  Decl_kinds.polymorphic ->
  Evd.evar_map -> Decl_kinds.logical_kind -> Names.constant
val declare_instance :
  Names.identifier ->
  Decl_kinds.polymorphic ->
  Evd.evar_map ->
  Context.rel_context ->
  Typeclasses.typeclass Term.puniverses -> Term.constr list -> Term.constr
val coq_unit : Term.constr lazy_t
val coq_tt : Term.constr lazy_t
val coq_prod : Term.constr lazy_t
val coq_pair : Term.constr lazy_t
val fresh_id_in_env :
  Names.Id.t list -> Names.Id.t -> Environ.env -> Names.Id.t
val fresh_id :
  Names.Id.t list ->
  Names.Id.t -> Proof_type.goal Tacmach.sigma -> Names.Id.t
val coq_eq : Globnames.global_reference Lazy.t
val coq_eq_refl : Globnames.global_reference lazy_t
val coq_heq : Globnames.global_reference lazy_t
val coq_heq_refl : Globnames.global_reference lazy_t
val coq_fix_proto : Globnames.global_reference lazy_t
val mkapp :
  Evd.evar_map ref ->
  Globnames.global_reference Lazy.t -> Term.constr array -> Term.constr
val refresh_universes_strict : Evd.evar_map ref -> Term.types -> Term.types
val mkEq :
  Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr -> Term.constr
val mkRefl : Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr
val mkHEq :
  Evd.evar_map ref ->
  Term.types -> Term.constr -> Term.types -> Term.constr -> Term.constr
val mkHRefl : Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr
val dummy_loc : Loc.t
val tac_of_string :
  string ->
  Tacexpr.r_dispatch Tacexpr.gen_tactic_arg list -> unit Proofview.tactic
val equations_path : string list
val coq_dynamic_ind : Term.constr lazy_t
val coq_dynamic_constr : Term.constr lazy_t
val coq_dynamic_type : Term.constr lazy_t
val coq_dynamic_obj : Term.constr lazy_t
val get_class : ('a * ('b * 'c)) option -> 'b
val functional_induction_class :
  unit -> Typeclasses.typeclass Term.puniverses
val functional_elimination_class :
  unit -> Typeclasses.typeclass Term.puniverses
val dependent_elimination_class :
  unit -> Typeclasses.typeclass Term.puniverses
val below_path : string list
val coq_have_class : Term.constr lazy_t
val coq_have_meth : Term.constr lazy_t
val coq_wellfounded_class : Term.constr lazy_t
val coq_wellfounded : Term.constr lazy_t
val coq_relation : Term.constr lazy_t
val coq_clos_trans : Term.constr lazy_t
val coq_id : Term.constr lazy_t
val list_path : string list
val coq_list_ind : Term.constr lazy_t
val coq_list_nil : Term.constr lazy_t
val coq_list_cons : Term.constr lazy_t
val coq_noconfusion_class : Term.constr lazy_t
val coq_inacc : Term.constr lazy_t
val coq_block : Term.constr lazy_t
val coq_hide : Term.constr lazy_t
val coq_add_pattern : Term.constr lazy_t
val coq_end_of_section_constr : Term.constr lazy_t
val coq_end_of_section : Term.constr lazy_t
val coq_notT : Term.constr lazy_t
val coq_ImpossibleCall : Term.constr lazy_t
val unfold_add_pattern : Proof_type.tactic lazy_t
val coq_dynamic_list : Term.constr lazy_t
val constrs_of_coq_dynamic_list :
  Term.constr -> (Term.constr * Term.constr) list
val subterm_relation_base : string
val head_of_constr : Term.constr -> Term.constr
val nowhere : 'a Locus.clause_expr
val lift_rel_contextn :
  int ->
  int ->
  Context.rel_context ->
  (Names.Name.t * Constr.constr option * Constr.constr) list
val lift_context :
  int ->
  Context.rel_context ->
  (Names.Name.t * Constr.constr option * Constr.constr) list
val unfold_head :
  Environ.env ->
  Names.Idset.t * Names.Cset.t -> Term.constr -> bool * Term.constr
val autounfold_first :
  Hints.hint_db_name list ->
  Locus.hyp_location option ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
