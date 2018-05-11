From Coq.Lists Require Import List.
From Equations Require Import Equations.

Inductive foo: Set :=
| Foo1 : list foo -> foo
| Foo2 : list foo -> foo.

Equations f (x: foo) : nat := {
  f (Foo1 l):= aux1 l;
  f (Foo2 l) := aux2 l
}
where aux1 (l : list foo) : nat := {
  aux1 [] := 1;
  aux1 (cons hd tl) := f hd + aux1 tl }
where aux2 (l : list foo) : nat := {
  aux2 [] := 1;
  aux2 (cons hd tl) := f hd + aux2 tl }.