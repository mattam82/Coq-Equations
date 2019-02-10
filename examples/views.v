(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(* end hide *)

From Equations Require Import Equations.
From Coq Require Import List Program.Syntax Arith Lia.

(** * Views using dependent pattern-matching

  The standard notion of pattern-matching in type theory requires to
  give a case for each constructor of the inductive type we are working
  on, even if the function acts the same on a subset of distinct
  constructors. The reason is that due to dependencies, it is not clear
  that two branches for distinct constructors can be factorized in general:
  the return types of branches could be unifiable or not, depending on the
  branch body.

  Rather than trying to internalise this notion in the pattern-matching
  algorithm we propose the use of views to encode this phenomenon.

  Suppose that we want to do case analysis on an inductive with
  three constructors but only want to single out the [cone] constructor during
  pattern-matching: *)

Inductive three := cone | ctwo | cthree.

(** The user can write a view function to implement this. First one needs to write
    a discriminator for the inductive type, indicating which cases are to be merged together:
 *)
Equations discr_three (c : three) : Prop :=
  discr_three cone := False;
  discr_three _ := True.

(** One can derive an inductive representing the view of [three] as [cone] and the two other
    [ctwo] and [cthree] cases lumbed together. *)
Inductive three_two_view : three -> Set :=
| three_one : three_two_view cone
| three_other c : discr_three c -> three_two_view c.

(** This view is obviously inhabited for any element in [three]. *)
Equations three_viewc c : three_two_view c :=
three_viewc cone := three_one;
three_viewc c := three_other c I.

(** Using a [with] clause one can pattern-match on the view argument to
    do case splitting on [three] using only two cases. In each branch,
    one can see that the [three] variable is determined by the view pattern.  *)
Equations onthree (c : three) : three :=
  onthree c with three_viewc c :=
  onthree ?(cone) three_one := cone;
  onthree ?(c) (three_other c Hc) := c.
