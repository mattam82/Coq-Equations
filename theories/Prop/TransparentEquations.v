(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** This module sets the set constants of Equations to transparent mode so
  that computation is possible inside Coq. *)

Require Import Equations.Prop.DepElim.

Global Transparent
       simplification_sigma2_uip
       simplification_K_uip
       simplify_ind_pack simplified_ind_pack.
