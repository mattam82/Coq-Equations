val ( = ) : int -> int -> bool
val solve_subterm_tac : unit -> unit Proofview.tactic
val refresh_universes : 'a -> 'a
val derive_subterm : Constr.pinductive -> unit
val list_chop : int -> 'a list -> 'a list * 'a list
val derive_below : Evd.evar_universe_context -> Names.inductive * 'a -> unit
