(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

type derive_record =
  { derive_name : string;
    derive_fn : poly:bool -> Names.GlobRef.t -> unit }

(** When the Derive expects a constr. *)                                 
val make_derive :
  (Environ.env -> Evd.evar_map -> poly:bool -> EConstr.constr -> unit) ->
  poly:bool -> Names.GlobRef.t -> unit

(** When the Derive works on inductive types only. *)                                 
val make_derive_ind :
  (Environ.env -> Evd.evar_map -> poly:bool -> Names.inductive * EConstr.EInstance.t -> unit) ->
  poly:bool -> Names.GlobRef.t -> unit
    
val register_derive : derive_record -> unit

(** Check if a given notion has been derived already for a given global reference. *)

val check_derive : string -> Names.GlobRef.t -> bool

val derive : poly:bool -> string list -> Names.GlobRef.t Loc.located list -> unit
