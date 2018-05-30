From Coq.Lists Require Import List.
From Equations Require Import Equations.

(* This type is from VST: https://github.com/PrincetonUniversity/VST/blob/v2.1/floyd/compact_prod_sum.v#L6 *)
Fixpoint compact_prod (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end.

(* The rest is a nonsensical, just to give a minimalistic reproducible example *)
Inductive Foo :=
| Foo1 : list Foo -> Foo
| Foo2 : list Foo -> Foo.

Equations foo_type (t : Foo) : Type :=
  foo_type (Foo1 fs) := compact_prod (List.map foo_type fs);
  foo_type (Foo2 fs) := compact_prod (List.map foo_type fs).

(* Moving val nato the return type, rather than having it as an argument might be unnecessary if
   https://github.com/mattam82/Coq-Equations/issues/73 was fixed *)
Equations (struct t) do_foo (t : Foo) : forall (val : foo_type t), nat := {
  do_foo (Foo1 fs) := fun val => do_foo1 fs val;
  do_foo (Foo2 fs) := fun val => do_foo2 fs val }

  where (struct fs)
    do_foo1 (fs:list Foo) : forall (val : compact_prod (map foo_type fs)), nat := {
    do_foo1 _ := fun val => 0}

  where (struct fs)
    do_foo2 (fs : list Foo) : forall val : compact_prod (List.map foo_type fs), nat := {
    do_foo2 nil := fun val => 0;
    do_foo2 (cons var nil) :=
      fun val => do_foo var val;
    do_foo2 _ := fun val => 0
}.