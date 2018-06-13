From Coq.Lists Require Import List.
From Equations Require Import Equations.

Inductive foo :=
| Sum : list foo -> foo.

Equations (struct t) do_foo1 (t: foo) : nat := {
  do_foo1 (Sum u) :=
        do_foo1_list2 u }

  where (struct ts)
    do_foo1_list (ts:list foo) : nat := {
    do_foo1_list nil := 0;
    do_foo1_list (cons t ts) := 0}

  where (struct fs)
    do_foo1_list2 (fs : list foo) : nat := {
    do_foo1_list2 _ := 0}

  where (struct t) do_foo2 (t : foo) : nat := {
  do_foo2 _ := 0 }

  where (struct ts)
    do_foo2_list (ts:list foo) : nat := {
    do_foo2_list nil := 0;
    do_foo2_list (cons t ts) <= (do_foo2_list ts) => {
      do_foo2_list (cons t _) _ := (do_foo1 t) + (do_foo2 t)}}.

Next Obligation. destruct fs; reflexivity. Defined.
Next Obligation. destruct t; reflexivity. Defined.
