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
  aux1 (cons hd tl) := f hd + aux1 tl + aux2 tl }

where aux2 (l : list foo) : nat := {
  aux2 [] := 1;
  aux2 (cons hd tl) := f hd + aux2 tl }.

(* where aux3 (l : list foo) : nat := { *)
(*   aux3 [] := 1; *)
(*   aux3 (cons hd tl) := f hd + aux3 tl }. *)

Next Obligation.
  assert ((forall x : foo, f_ind x (f x)) ->
  (forall l : list foo, f_ind_1 l (aux1 l)) /\
  (forall l : list foo, f_ind_2 l (aux2 l))).
  intros.
  split.
  fix H2 1. intros l.
  assert(forall l : list foo, f_ind_2 l (aux2 l)).
  fix H3 1. intros l'. destruct l'.
  constructor.
  constructor.
  apply H.
  apply H3.
  destruct l; constructor. apply H.
  apply H2. apply H0.
  fix H3 1; intros l; destruct l; constructor; auto.
  assert (forall x, f_ind x (f x)).
  fix H1 1.
  specialize (H H1).
  destruct H.
  intros x. destruct x.
  simpl. constructor.
  apply H.
  constructor.
  apply H0.
  intuition.
Defined.

Module Three.

Equations f (x: foo) : nat := {
  f (Foo1 l):= aux1 l;
  f (Foo2 l) := aux2 l
}

where aux1 (l : list foo) : nat := {
  aux1 [] := 1;
  aux1 (cons hd tl) := f hd + aux1 tl + aux2 tl }

where aux2 (l : list foo) : nat := {
  aux2 [] := 1;
  aux2 (cons hd tl) := f hd + aux2 tl }

where aux3 (l : list foo) : nat := {
  aux3 [] := 1;
  aux3 (cons hd tl) := f hd + aux3 tl }.

Axiom cheat : forall {A}, A.
Next Obligation. apply cheat. Defined.
End Three.