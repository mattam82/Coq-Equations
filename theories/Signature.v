(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Signatures for dependent types. 
   
   A signature for [A] is a sigma-type in which any [A] 
   can be packed. *)

Class Signature (fam : Type) (signature_index : Type) := {
  signature : signature_index -> Type ;
  signature_pack : fam -> { i : signature_index & signature i }
}.

Notation " x ~=~ y " := (signature_pack x = signature_pack y) (at level 90).

Notation " '(' x '&' y ')' " := (existT _ x y) : equations. 
