(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

type derive_record =
  { derive_name : string;
    derive_fn : polymorphic:Decl_kinds.polymorphic -> Globnames.global_reference -> unit }

(** When the Derive expects a constr. *)                                 
val make_derive :
  (Environ.env -> Evd.evar_map -> polymorphic:Decl_kinds.polymorphic -> Constr.constr -> unit) ->
  polymorphic:bool -> Globnames.global_reference -> unit

(** When the Derive works on inductive types only. *)                                 
val make_derive_ind :
  (Environ.env -> Evd.evar_map -> polymorphic:Decl_kinds.polymorphic -> Constr.pinductive -> unit) ->
  polymorphic:bool -> Globnames.global_reference -> unit
    
val register_derive : derive_record -> unit

val derive : string list -> Globnames.global_reference Loc.located list -> unit
