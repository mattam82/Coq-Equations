From Coq.Lists Require Import List.
From Equations Require Import Equations.

Inductive foo :=
| List : list foo -> foo.

Equations do_foo1 (t: foo) : nat := {
  do_foo1 (List ss) := do_foo1_list ss }

  where do_foo1_list (ts:list foo) : nat := {
    do_foo1_list nil := 0;
    do_foo1_list (cons t ts) := do_foo1 t + do_foo1_list ts }

  where do_foo2 (t : foo) : nat := {

  do_foo2 (List nil) := 0;
  do_foo2 (List (cons t ts)) := do_foo2 t }

  where do_foo2_list (ts:list foo) : nat := {
    do_foo2_list nil := 0;
    do_foo2_list (cons t ts) := do_foo2_list ts }.
Definition check := do_foo1_elim.