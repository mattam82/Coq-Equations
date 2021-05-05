(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

type derive_record =
  { derive_name : string;
    derive_fn : pm:Declare.OblState.t -> poly:bool -> Names.GlobRef.t -> Declare.OblState.t }

(** When the Derive expects a constr. *)
val make_derive :
  (pm:Declare.OblState.t -> Environ.env -> Evd.evar_map -> poly:bool -> EConstr.constr -> Declare.OblState.t) ->
  pm:Declare.OblState.t ->
  poly:bool -> Names.GlobRef.t -> Declare.OblState.t

(** When the Derive works on inductive types only. *)
val make_derive_ind :
  (pm:Declare.OblState.t -> Environ.env -> Evd.evar_map -> poly:bool -> Names.inductive * EConstr.EInstance.t -> Declare.OblState.t) ->
  pm:Declare.OblState.t ->
  poly:bool -> Names.GlobRef.t -> Declare.OblState.t

val register_derive : derive_record -> unit

(** Check if a given notion has been derived already for a given global reference. *)

val check_derive : string -> Names.GlobRef.t -> bool

val derive :
  pm:Declare.OblState.t
  -> poly:bool
  -> string list
  -> Names.GlobRef.t Loc.located list
  -> Declare.OblState.t
