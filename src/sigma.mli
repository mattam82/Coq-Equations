val is_global : Globnames.global_reference -> Term.constr -> bool
val coq_sigma : Coqlib.coq_sigma_data Lazy.t
val mkAppG :
  Evd.evar_map ref ->
  Globnames.global_reference -> Term.constr array -> Term.constr
val applistG :
  Evd.evar_map ref ->
  Globnames.global_reference -> Term.constr list -> Term.constr
val mkSig :
  Evd.evar_map ref -> Names.Name.t * Term.types * Term.constr -> Term.constr
val constrs_of_coq_sigma :
  Environ.env ->
  Evd.evar_map ref ->
  Term.constr ->
  Term.constr -> (Names.name * Term.constr * Term.constr * Term.constr) list
val decompose_coq_sigma : Term.constr -> (Term.constr * Term.constr) option
val decompose_indapp :
  Term.constr -> Term.constr array -> Term.constr * Term.constr array
val sigT : Coqlib.coq_sigma_data Lazy.t
val sigT_info : Term.case_info lazy_t
val telescope :
  Evd.evar_map ref ->
  (Names.Name.t * 'a option * Constr.constr) list ->
  Term.constr * (Names.Name.t * Term.constr option * Term.constr) list *
  Term.constr
val sigmaize :
  ?liftty:int ->
  Environ.env ->
  Evd.evar_map ref ->
  Term.constr ->
  Term.constr * Term.constr * Constr.constr list * Term.constr *
  Term.constr * Term.constr * Term.constr
val ind_name : Names.inductive -> Names.Id.t
val signature_ref : Term.constr lazy_t
val signature_sig : Term.constr lazy_t
val signature_pack : Term.constr lazy_t
val signature_class : unit -> Typeclasses.typeclass Term.puniverses
val declare_sig_of_ind : Environ.env -> Names.inductive -> Term.constr
val get_signature :
  Environ.env -> Evd.evar_map -> Term.constr -> Term.constr * Term.constr
val pattern_sigma :
  Term.constr ->
  Names.Id.t -> Environ.env -> Evd.evar_map -> unit Proofview.tactic
val curry_hyp :
  Evd.evar_map ->
  Term.constr -> Term.types -> (Term.constr * Term.types) option
