From Equations Require Import Equations.
Require Import List.
Require Import Program.
Reserved Notation "x +++ y" (at level 50).

Equations app {A} (l : list A) : list A -> list A :=
  { [] +++ y := y;
    (x :: xs) +++ y := x :: (xs +++ y) }

where foo : nat -> nat :=
{foo 0 := 0; foo (S n) := foo n}

where "x +++ y" := (app x y).

Check nil +++ nil.

Equations plus : nat -> nat -> nat :=
{ 0   + n := n;
  S m + n := S (m + n) }
where "x + y" := (plus x y).

(* Local notation in where *)
Reserved Notation "x '++++' y" (at level 0).

Equations rev {A} : list A -> list A :=
  rev l := [] ++++ l
   where "x ++++ y" := (rev_aux x y)
   where rev_aux : list A -> list A -> list A :=
       { acc ++++ [] := acc;
         acc ++++ (x :: l) := (x :: acc) ++++ l }.

Print Scopes.

Require Import Arith NArith.
Local Open Scope N_scope.
Check (_ - 0).

(** Parsing works with scopes as well *)
Equations scope_match (n : nat) : nat :=
  scope_match 0 := 0;
  scope_match (S n) := S (scope_match (n - 0)).

Equations scope_match_N (n : N) : N :=
  scope_match_N 0 := 0;
  scope_match_N (N.pos n) := N.pos n.
