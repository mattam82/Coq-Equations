(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** {6 Where clauses} *)

From Equations Require Import Equations Fin DepElimDec.

Equations(nocomp) f (n : nat) : nat :=
f 0 := 0 ;
f (S n) := if g n then f n else S (f n)

where g (n : nat) : bool :=
g 0 := true ;
g (S _) := false.
