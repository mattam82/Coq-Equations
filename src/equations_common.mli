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

(** Context lifting *)
val lift_rel_contextn :
  int -> int -> Context.rel_context -> Context.rel_context

val lift_context : int -> Context.rel_context -> Context.rel_context

val lift_list : constr list -> constr list
val lift_constrs : int -> constr list -> constr list

(** Evars *)
val new_untyped_evar : unit -> Evd.evar

(** Checking *)
val check_term :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.types -> unit
val check_type : Environ.env -> Evd.evar_map -> Term.types -> unit
val typecheck_rel_context :
  Evd.evar_map -> Context.rel_context -> unit

val e_conv :
  env -> Evd.evar_map ref -> constr -> constr -> bool

val e_type_of : env -> Evd.evar_map ref -> constr -> types
						
val reference_of_global : Globnames.global_reference -> Libnames.reference

(** Term manipulation *)

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

val ids_of_constr :
  ?all:bool -> Idset.t -> constr -> Idset.t
val deps_of_var : Id.t -> env -> Idset.t
val idset_of_list : Id.t list -> Idset.t

val decompose_indapp :
  constr -> constr array -> constr * constr array

val refresh_universes_strict : Evd.evar_map ref -> Term.types -> Term.types

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

(** Standard datatypes *)
val coq_unit : Term.constr lazy_t
val coq_tt : Term.constr lazy_t
val coq_prod : Term.constr lazy_t
val coq_pair : Term.constr lazy_t

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
