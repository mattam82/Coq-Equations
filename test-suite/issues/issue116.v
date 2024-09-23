From Stdlib.Lists Require Import List.
From Equations Require Import Equations.

Inductive foo :=
| Sum : list foo -> foo.

Equations do_foo1 (t: foo) : nat (* by struct t *) := {
  do_foo1 (Sum u) :=
        do_foo1_list u }


  where do_foo2 (t : foo) : nat by struct t := {
  do_foo2 (Sum nil) := 0;
  do_foo2 (Sum (l :: tl)) := do_foo2 l }

  where
    do_foo1_list (ts:list foo) : nat by struct ts := {
    do_foo1_list nil := 0;
    do_foo1_list (cons t ts) := do_foo1 t + (do_foo1_list ts)}


  where
    do_foo2_list (ts:list foo) : nat := {
    do_foo2_list nil := 0;
    do_foo2_list (cons t ts) with (do_foo2_list ts) => {
      do_foo2_list (cons t _) _ := (do_foo1 t) + (do_foo2 t)}}.

Definition check := do_foo1_elim.