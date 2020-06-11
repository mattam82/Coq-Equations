From Equations Require Import Equations. 
Require Import List.
Import ListNotations.
Inductive T := C : list T -> T.
Show Obligation Tactic.
Set Equations Debug.
Equations f (p : bool) (e : T) : T by struct e := {
  f false e := e ;
  f p (C xs) :=
    let xs := g true xs in
    C xs }
where g (p : bool) (xs : list T) : list T by struct xs := {
  g false xs := xs ;
  g _ [] := [];
  g p (x :: xs) :=
    let x := c true x in
    let xs := g true xs in
    x :: xs }
where c (p : bool) (x : T) : T by struct x := {
  c false x := x ;
  c p x :=
    let x := f true x in
    x }.
Next Obligation. destruct x; auto. Defined.
Next Obligation. destruct x; auto. Defined.
Next Obligation. destruct xs; auto. Defined.
About f_elim.