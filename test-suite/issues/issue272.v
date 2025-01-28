From Equations.Prop Require Import Equations.

(* If it's the full definition from the start, works fine *)
(* Equations even (n : nat) : bool := { *)
(*   even (S n) := odd n; *)
(*   even 0 := true } *)
(* with odd (n : nat) : bool := { *)
(*   odd 0 := false ; *)
(*   odd (S n) := even n}. *)

(* However, mutual definition fails when one of the function *)
(* is independent from the others *)
Equations even (n : nat) : bool := {even n := false }
with odd (n : nat) : bool by struct n := {
  odd 0 := false ;
  odd (S n) := even n}.
(* The variable even was not found in the current environment. *)

(* This is bad because it prevents iterated refinement of code *)
(* and it also prevents from mixing code with proof mode *)
Fail Equations? even (n : nat) : bool := {
  even (S n) := odd n;
  even 0 := true }
with odd (n : nat) : bool by struct n := {
  odd n := _}.
(* The variable odd was not found in the current environment. *)

(* Moreover the error gets even more mysterious when all *)
(* the putative mutually defined functions are independent *)
Module NoApparentRec. 
Equations even (n : nat) : bool by struct n := {
  even n := true }
with odd (n : nat) : bool by struct n := {
  odd n := false}.
  Next Obligation. destruct n; auto. Defined.
End NoApparentRec.
(* Cannot define even mutually with other programs *)
