(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

val ( = ) : int -> int -> bool
val solve_subterm_tac : unit -> unit Proofview.tactic
val refresh_universes : 'a -> 'a
val derive_subterm : Constr.pinductive -> unit
val list_chop : int -> 'a list -> 'a list * 'a list
val derive_below : Evd.evar_universe_context -> Names.inductive * 'a -> unit
