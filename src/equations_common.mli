(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names

val debug : bool

(* Tactics *)
val to82 : 'a Proofview.tactic -> Proofview.V82.tac
val of82 : Proofview.V82.tac -> unit Proofview.tactic

(* Point-free composition *)
val ( $ ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val ( &&& ) : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd

val id : 'a -> 'a

val array_remove_last : 'a array -> 'a array
val array_chop_last : 'a array -> 'a array * 'a array
val rev_assoc : ('a -> 'b -> bool) -> 'a -> ('c * 'b) list -> 'c
val array_filter_map : ('a -> 'b option) -> 'a array -> 'b array

(* All the tails of [x1 ... xn] : [[xn]; [xn-1; xn] ...[x2 .. xn]] *)
val proper_tails : 'a list -> 'a list list

(* Stop at the first Some *)
val list_find_map_i : (int -> 'a -> 'b option) -> int -> 'a list -> 'b option

val head_of_constr : Term.constr -> Term.constr
val nowhere : 'a Locus.clause_expr
val dummy_loc : Loc.t
type 'a located = 'a Loc.located

(** Fresh names *)
val fresh_id_in_env :
  Names.Id.t list -> Names.Id.t -> Environ.env -> Names.Id.t
val fresh_id :
  Names.Id.t list ->
  Names.Id.t -> Proof_type.goal Tacmach.sigma -> Names.Id.t

(** Refer to a tactic *)
val tac_of_string :
  string ->
  Tacexpr.r_dispatch Tacexpr.gen_tactic_arg list -> unit Proofview.tactic

type rel_declaration = Context.Rel.Declaration.t
type rel_context = Context.Rel.t
type named_declaration = Context.Named.Declaration.t
type named_context = Context.Named.t
       
(** Context lifting *)
val lift_rel_contextn :
  int -> int -> rel_context -> rel_context

val lift_context : int -> rel_context -> rel_context

val lift_list : constr list -> constr list
val lift_constrs : int -> constr list -> constr list

(** Evars *)
val new_untyped_evar : unit -> Evd.evar

(** Checking *)
val check_term :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.types -> unit
val check_type : Environ.env -> Evd.evar_map -> Term.types -> unit
val typecheck_rel_context :
  Evd.evar_map -> rel_context -> unit

val e_conv :
  env -> Evd.evar_map ref -> constr -> constr -> bool

val e_type_of : env -> Evd.evar_map ref -> constr -> types
						     
val reference_of_global : Globnames.global_reference -> Libnames.reference

(** Term manipulation *)

val mkNot : Term.constr -> Term.constr
val mkProd_or_subst :
  rel_declaration ->
  Term.types -> Term.types
val mkProd_or_clear : rel_declaration -> Term.constr -> Constr.constr
val it_mkProd_or_clear :
  Term.constr -> rel_declaration list -> Term.constr
val mkLambda_or_subst :
  rel_declaration ->
  Term.constr -> Term.constr
val mkLambda_or_subst_or_clear :
  rel_declaration ->
  Term.constr -> Term.constr
val mkProd_or_subst_or_clear :
  rel_declaration ->
  Term.constr -> Term.types
val it_mkProd_or_subst :
  Term.types -> rel_declaration list -> Term.constr
val it_mkProd_or_clean :
  Constr.constr ->
  rel_context -> Term.constr
val it_mkLambda_or_subst :
  Term.constr -> rel_declaration list -> Term.constr
val it_mkLambda_or_subst_or_clear :
  Term.constr ->
  (rel_declaration) list -> Term.constr
val it_mkProd_or_subst_or_clear :
  Term.constr ->
  (rel_declaration) list -> Term.constr

val ids_of_constr :
  ?all:bool -> Idset.t -> constr -> Idset.t
val deps_of_var : Id.t -> env -> Idset.t
val idset_of_list : Id.t list -> Idset.t

val decompose_indapp :
  constr -> constr array -> constr * constr array

val refresh_universes_strict : Evd.evar_map ref -> Term.types -> Term.types

val new_global : Evd.evar_map -> Globnames.global_reference -> Evd.evar_map * Term.constr
                                                                 
(** {6 Linking to Coq} *)

val find_constant : Coqlib.message -> string list -> string -> Term.constr
val contrib_name : string
val init_constant : string list -> string -> Term.constr
val init_reference : string list -> string -> Globnames.global_reference
val gen_constant : string list -> string -> constr

val get_class : Term.constr -> Typeclasses.typeclass Term.puniverses

val make_definition :
  ?opaque:'a ->
  ?poly:Decl_kinds.polymorphic ->
  Evd.evar_map ref ->
  ?types:Term.constr -> Term.constr -> Safe_typing.private_constants Entries.definition_entry

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
  rel_context ->
  Typeclasses.typeclass Term.puniverses -> Term.constr list -> Term.constr

(** Standard datatypes *)

type logic_ref = Globnames.global_reference lazy_t
							       
type logic = {
  logic_eqty : logic_ref;
  logic_eqrefl: logic_ref;
  logic_sort : sorts_family;
  logic_zero : logic_ref;
  logic_one : logic_ref;
  logic_one_val : logic_ref;
  (* logic_sigma : logic_ref; *)
  (* logic_pair : logic_ref; *)
  (* logic_fst : logic_ref; *)
  (* logic_snd : logic_ref; *)
}

val set_logic : logic -> unit
val prop_logic : logic
val type_logic : logic

val get_sort : unit -> sorts_family
val get_eq : unit -> Globnames.global_reference lazy_t
val get_eq_refl : unit -> Globnames.global_reference lazy_t

val get_one : unit -> Globnames.global_reference lazy_t
val get_one_prf : unit -> Globnames.global_reference lazy_t
val get_zero : unit -> Globnames.global_reference lazy_t

val coq_unit : Globnames.global_reference lazy_t
val coq_tt : Globnames.global_reference lazy_t
						  
val coq_prod : Term.constr lazy_t
val coq_pair : Term.constr lazy_t

val coq_sigma : Globnames.global_reference lazy_t
val coq_sigmaI : Globnames.global_reference lazy_t
val coq_pr1 : Names.projection lazy_t
val coq_pr2 : Names.projection lazy_t
			    
val coq_zero : constr lazy_t
val coq_succ : constr lazy_t
val coq_nat : constr lazy_t
val coq_nat_of_int : int -> constr
val int_of_coq_nat : constr -> int

val coq_eq : Globnames.global_reference Lazy.t
val coq_eq_refl : Globnames.global_reference lazy_t
val coq_heq : Globnames.global_reference lazy_t
val coq_heq_refl : Globnames.global_reference lazy_t
val coq_fix_proto : Globnames.global_reference lazy_t
val mkapp :
  Evd.evar_map ref ->
  Globnames.global_reference Lazy.t -> Term.constr array -> Term.constr
val mkEq :
  Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr -> Term.constr
val mkRefl : Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr
val mkHEq :
  Evd.evar_map ref ->
  Term.types -> Term.constr -> Term.types -> Term.constr -> Term.constr
val mkHRefl : Evd.evar_map ref -> Term.types -> Term.constr -> Term.constr

(** Bindings to theories/ files *)

val equations_path : string list
val below_path : string list
val list_path : string list
val subterm_relation_base : string

val functional_induction_class :
  unit -> Typeclasses.typeclass Term.puniverses
val functional_elimination_class :
  unit -> Typeclasses.typeclass Term.puniverses
val dependent_elimination_class :
  unit -> Typeclasses.typeclass Term.puniverses

val coq_wellfounded_class : Term.constr lazy_t
val coq_wellfounded : Term.constr lazy_t
val coq_relation : Term.constr lazy_t
val coq_clos_trans : Term.constr lazy_t
val coq_id : Term.constr lazy_t
val coq_list_ind : Term.constr lazy_t
val coq_list_nil : Term.constr lazy_t
val coq_list_cons : Term.constr lazy_t
val coq_noconfusion_class : Globnames.global_reference lazy_t
val coq_inacc : Term.constr lazy_t
val coq_block : Term.constr lazy_t
val coq_hide : Term.constr lazy_t
val coq_add_pattern : Term.constr lazy_t
val coq_end_of_section_constr : Term.constr lazy_t
val coq_end_of_section : Term.constr lazy_t
val coq_notT : Term.constr lazy_t
val coq_ImpossibleCall : Term.constr lazy_t
val unfold_add_pattern : unit Proofview.tactic lazy_t

val below_tactics_path : Names.dir_path
val below_tac : string -> Names.kernel_name
val tacident_arg :
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : 'c; name : 'd; pattern : 'e;
    reference : Libnames.reference; tacexpr : 'f; term : 'g > Tacexpr.gen_tactic_arg
val tacvar_arg :
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : Genarg.rlevel; name : 'c;
    pattern : 'd; reference : 'e; tacexpr : 'f; term : 'g > Tacexpr.gen_tactic_arg
val rec_tac :
  'f ->
  Names.Id.t ->
  < constant : 'a; dterm : 'b; level : Genarg.rlevel; name : 'c;
    pattern : 'd; reference : Libnames.reference; tacexpr : 'e; term : 'f; >
	   Tacexpr.gen_tactic_expr
val rec_wf_tac :
  'a ->
  Names.Id.t ->
  'a ->
  < constant : 'b; dterm : 'c; level : Genarg.rlevel; name : 'd;
    pattern : 'e; reference : Libnames.reference; tacexpr : 'f; term : 'a;>
	   Tacexpr.gen_tactic_expr
val unfold_recursor_tac : unit -> unit Proofview.tactic
val equations_tac_expr :
  unit ->
  < constant : 'a; dterm : 'b; level : 'c; name : 'd; pattern : 'e;
    reference : Libnames.reference; tacexpr : 'f; term : 'g >
								    Tacexpr.gen_tactic_expr
val solve_rec_tac_expr :
  unit ->
  < constant : 'a; dterm : 'b; level : 'c; name : 'd; pattern : 'e;
    reference : Libnames.reference; tacexpr : 'f; term : 'g >
								    Tacexpr.gen_tactic_expr
val equations_tac : unit -> unit Proofview.tactic
val set_eos_tac : unit -> unit Proofview.tactic
val solve_rec_tac : unit -> unit Proofview.tactic
val find_empty_tac : unit -> unit Proofview.tactic
val pi_tac : unit -> unit Proofview.tactic
val noconf_tac : unit -> unit Proofview.tactic
val eqdec_tac : unit -> unit Proofview.tactic
val simpl_equations_tac : unit -> unit Proofview.tactic
val solve_equation_tac : Globnames.global_reference -> unit Proofview.tactic
val impossible_call_tac :
  Globnames.global_reference -> Tacexpr.glob_tactic_expr
val depelim_tac : Names.Id.t -> unit Proofview.tactic
val do_empty_tac : Names.Id.t -> unit Proofview.tactic
val depelim_nosimpl_tac : Names.Id.t -> unit Proofview.tactic
val simpl_dep_elim_tac : unit -> unit Proofview.tactic
val depind_tac : Names.Id.t -> unit Proofview.tactic

(** Unfold the first occurrence of a constant declared unfoldable in db
  (with Hint Unfold) *)
val autounfold_first :
  Hints.hint_db_name list ->
  Locus.hyp_location option ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

type hintdb_name = string
val db_of_constr : constr -> hintdb_name
val dbs_of_constrs : constr list -> hintdb_name list

val pr_smart_global :
  Libnames.reference Misctypes.or_by_notation -> Pp.std_ppcmds
val string_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> string
val ident_of_smart_global :
  Libnames.reference Misctypes.or_by_notation -> identifier

val pf_get_type_of : Goal.goal Evd.sigma -> constr -> types

val move_after_deps : Names.Id.t -> Constr.t -> unit Proofview.tactic

val extended_rel_vect : int -> rel_context -> constr array
val extended_rel_list : int -> rel_context -> constr list
val to_tuple : rel_declaration -> Names.Name.t * Constr.t option * Constr.t
val to_named_tuple : named_declaration -> Names.Id.t * Constr.t option * Constr.t
val of_tuple : Names.Name.t * Constr.t option * Constr.t -> rel_declaration
val of_named_tuple : Names.Id.t * Constr.t option * Constr.t -> named_declaration

val get_type : rel_declaration -> Constr.t
val get_name : rel_declaration -> Names.Name.t
val get_value : rel_declaration -> Constr.t option
val make_assum : Names.Name.t -> Constr.t -> rel_declaration
val make_def : Names.Name.t -> Constr.t option -> Constr.t -> rel_declaration
val make_named_def : Names.Id.t -> Constr.t option -> Constr.t -> named_declaration
val to_context : (Names.Name.t * Constr.t option * Constr.t) list -> rel_context

val localdef : Constr.t -> Entries.local_entry
val localassum : Constr.t -> Entries.local_entry
val named_of_rel_context : (unit -> Names.Id.t) -> rel_context -> Vars.substl * Term.constr list * named_context
val rel_of_named_context : named_context -> rel_context * Names.Id.t list
val subst_rel_context : int -> Vars.substl -> rel_context -> rel_context
val get_id : named_declaration -> Names.Id.t
val get_named_type : named_declaration -> Constr.t
val get_named_value : named_declaration -> Constr.t option

val lookup_rel : int -> rel_context -> rel_declaration
val fold_named_context_reverse : ('a -> named_declaration -> 'a) -> init:'a -> named_context -> 'a
val map_rel_context : (Constr.t -> Constr.t) -> rel_context -> rel_context
val map_rel_declaration : (Constr.t -> Constr.t) -> rel_declaration -> rel_declaration
val map_named_declaration : (Constr.t -> Constr.t) -> named_declaration -> named_declaration

val to_evar_map : 'a Sigma.t -> Evd.evar_map
val of_evar_map : Evd.evar_map -> 'a Sigma.t

val pp : Pp.std_ppcmds -> unit
val user_err_loc : (Loc.t * string * Pp.std_ppcmds) -> 'a
val error : string -> 'a
val errorlabstrm : string -> Pp.std_ppcmds -> 'a
val is_anomaly : exn -> bool
val print_error : exn -> Pp.std_ppcmds
val anomaly : ?label:string -> Pp.std_ppcmds -> 'a
                                
val nf_betadeltaiota : Reductionops.reduction_function

val subst_telescope : Constr.constr -> rel_context -> rel_context
val subst_in_ctx : int -> Term.constr -> rel_context -> rel_context
val set_in_ctx : int -> Term.constr -> rel_context -> rel_context

val evar_declare : named_context_val ->
  Evd.evar -> 
  types -> ?src:(Loc.t * Evar_kinds.t) -> Evd.evar_map -> Evd.evar_map

val new_evar :            Environ.env ->
           Evd.evar_map ->
           ?src:Loc.t * Evar_kinds.t ->
           Term.types -> Evd.evar_map * Term.constr

val new_type_evar :            Environ.env ->
           Evd.evar_map -> 
           ?src:Loc.t * Evar_kinds.t -> Evd.rigid ->
           Evd.evar_map * (Term.constr * Term.sorts)

val empty_hint_info : 'a Vernacexpr.hint_info_gen

val evar_absorb_arguments :
  Environ.env -> Evd.evar_map ->
  Term.existential ->
  Term.constr list -> Evd.evar_map * Term.existential
