(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** This module sets the set constants of Equations to opaque mode so
  that computation is not possible inside Coq, the tactics need this
  to solve obligations. *)

From Equations Require Import DepElim.

Global Opaque simplification_existT2 simplification_existT2_dec
       simplification_sigma2 simplification_sigma2_dec
       simplification_sigma2_dec_point
       simplification_heq simplification_K simplification_K_dec
       simplify_ind_pack simplified_ind_pack Id_simplification_sigma2.
