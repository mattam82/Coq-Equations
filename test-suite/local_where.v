Require Import Program.Basics Program.Tactics.
Require Import Equations.Equations.

Equations foo (n : nat) : nat :=
foo n := n + k 0
  where k (x : nat) : nat :=
  { k 0 := 0 ; k (S n') := n }.

Variable f : nat -> (nat * nat).

Equations foo' (n : nat) : nat :=
foo' 0 := 0;
foo' (S n) := n + k (f 0) (0, 0)

  where k (x : nat * nat) (y : nat * nat) : nat :=
  { k (x, y) (x', y') := x }.

Variable kont : ((nat * nat) -> nat) -> nat.

Equations foo'' (n : nat) : nat :=
foo'' 0 := 0;
foo'' (S n) := n + kont absw

  where absw : (nat * nat) -> nat :=
  absw (x, y) := x.

Equations foo3 (n : nat) : nat :=
foo3 0 := 0;
foo3 (S n) := n + kont (λ{ | (x, y) := x }).

Variant index : Set := i1 | i2.

Derive NoConfusion for index.

Inductive expr : index -> Set :=
| e1 : expr i1
| e2 {i} : expr i -> expr i2.

Derive Signature NoConfusion NoConfusionHom for expr.

Variable kont' : forall x : index, (expr x -> nat) -> nat.

Equations foo4 {i} (n : expr i) : nat :=
foo4 e1 := 0;
foo4 (@e2 i e) := absw e

  where absw : forall {i}, expr i -> nat :=
  absw e1 := 0;
  absw (e2 _) := 0.

Equations foo5 {i} (n : expr i) : nat :=
foo5 e1 := 0;
foo5 (@e2 i e) := absw e

  where absw : expr i -> nat :=
  absw e1 := 0;
  absw (e2 e') := foo5 e'.

Equations foo6 : nat :=
  foo6 := 0.

Equations foo7 : nat -> nat :=
  foo7 x := if bla then 0 else 1 + bla' eq_refl

  where bla : bool :=
  { bla := true }

  where bla' : bla = bla -> nat :=
  { bla' H := 1 + if bla then 1 else 2 }.

Equations foo8 : nat -> nat :=
{ foo8 0 := 0;
  foo8 (S x) := if bla then 0 else 1 + bla' eq_refl + foo8 x

  where bla : bool :=
  { bla := true }

  where bla' : bla = bla -> nat :=
  { bla' H := 1 + if bla then 1 else 2 + foo8 x }

  where bla'' : nat :=
  { bla'' := 3 + bla' eq_refl + baz 4 } }

where baz : nat -> nat :=
baz 0 := 0;
baz (S n) := baz n.

Notation "{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99) : type_scope.
Notation "{ x & y }" := (@sigma _ (fun x : _ => y)%type) (x at level 99) : type_scope.

Notation "&( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
    (right associativity, at level 4,
     format "&( x ,  .. ,  y  ,  z )").
Obligation Tactic := idtac.

Equations foo9 : { x: nat & x = 0 } :=
foo9 := &(lhs, rhs)
   where lhs : nat :=
    { lhs := 0 }

   where rhs : lhs = 0 :=
   { rhs := eq_refl }.
