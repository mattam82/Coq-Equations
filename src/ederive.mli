(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

type derive_record =
  { derive_name : string;
    derive_fn : polymorphic:Decl_kinds.polymorphic -> Names.GlobRef.t -> unit }

(** When the Derive expects a constr. *)                                 
val make_derive :
  (Environ.env -> Evd.evar_map -> polymorphic:Decl_kinds.polymorphic -> EConstr.constr -> unit) ->
  polymorphic:bool -> Names.GlobRef.t -> unit

(** When the Derive works on inductive types only. *)                                 
val make_derive_ind :
  (Environ.env -> Evd.evar_map -> polymorphic:Decl_kinds.polymorphic -> Names.inductive * EConstr.EInstance.t -> unit) ->
  polymorphic:bool -> Names.GlobRef.t -> unit
    
val register_derive : derive_record -> unit

val derive : poly:bool -> string list -> Names.GlobRef.t Loc.located list -> unit
