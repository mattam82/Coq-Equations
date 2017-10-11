Require Import Equations.

Inductive foo : Set :=
| c0 : nat -> foo
| c1 : bar -> bar -> foo
(* | c3 : bar -> foo *)
| c2 : foo -> foo
with bar : Set :=
| d0 : nat -> bar
| d1 : foo -> bar.

(* Inductive foo_foo_subterm : foo -> foo -> Prop := *)
(* | c1_sub0 b f g : *)
(*     foo_bar_subterm f b -> foo_foo_subterm f (c1 b g) *)
(* | c1_sub1 b f g : foo_bar_subterm b g -> foo_foo_subterm b (c1 f g) *)
(* | c2_sub x : foo_foo_subterm x (c2 x) *)
(* with foo_bar_subterm : foo -> bar -> Prop := *)
(* | d1_sub f : foo_bar_subterm f (d1 f) *)

(* with bar_bar_subterm : bar -> bar -> Prop := *)
(* | d1b b f : bar_foo_subterm b f -> bar_bar_subterm b (d1 f) *)
     
(* with bar_foo_subterm : bar -> foo -> Prop := *)
(* | c1b b q : bar_foo_subterm b (c1 b q) *)
(* | c2b b q :bar_foo_subterm b (c1 q b). *)

(* Scheme foo_foo_s := Induction for foo_foo_subterm Sort Prop *)
(* with foo_bar_s := Induction for foo_bar_subterm Sort Prop *)
(* with bar_bar_s := Induction for bar_bar_subterm Sort Prop *)
(* with bar_foo_s := Induction for bar_foo_subterm Sort Prop. *)

(* Combined Scheme foo_bar_subterm from foo_foo_s, foo_bar_s, bar_bar_s, bar_foo_s. *)
                                            
Scheme foo_bar_mut := Induction for foo Sort Set
with foo_bar_mut' := Induction for bar Sort Set.

Equations fn (x : foo) : nat :=
fn (c0 x) := x; 
fn (c2 f) := fn f;
(* fn (c3 b) := fnb b; *)
fn (c1 b b') := fnb b + fnb b'
where fnb (x : bar) : nat :=
  fnb (d0 x) := x;
  fnb (d1 f) := fn f.
Next Obligation.
  revert x. fix f 1.
  destruct x. constructor. Transparent fn. unfold fn.
  assert(forall x: bar, fn_ind_1 b b0 x (fn_obligation_1 fn b b0 x)).
  fix g 1. destruct x. simpl. constructor. constructor. apply f.
  constructor. apply H. apply H.
  simpl. constructor. apply f.
Defined.

Eval compute in fn.
(* Combined Scheme foo_bar from foo_bar_mut, foo_bar_mut'. *)

Section mutrec.
  Variables foo_bar_rec : foo -> nat.
  Variables foo_bar_rec' : bar -> nat.
  
  Equations foo_bar_fn (x : foo) : nat :=
  foo_bar_fn (c0 x) := x;
  foo_bar_fn (c1 b b') := foo_bar_rec' b + foo_bar_rec' b';
  foo_bar_fn (c2 f) := foo_bar_rec f.

  Equations foo_bar_fn' (x : bar) : nat :=
  foo_bar_fn' (d0 x) := x;
  foo_bar_fn' (d1 b) := foo_bar_fn b.
End mutrec.

Definition foobarknot :=
  fix F (x : foo) := foo_bar_fn F G x
  with G (x : bar) := foo_bar_fn' F G x for F.

