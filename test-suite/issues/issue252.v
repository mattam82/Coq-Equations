Require Import Equations.Equations.

Inductive vec (A:Type) : nat -> Type :=
  | nil : vec A 0
  | cons : forall n, A -> vec A n -> vec A (S n).

Arguments nil {A}.
Arguments cons {A n}.

Derive Signature for vec.

Notation "x :: v" := (cons x v).
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )).

Equations head {A n} (v : vec A (S n)) : A :=
head (x :: _) := x.

Equations tail {A n} (v : vec A (S n)) : vec A n :=
tail (_ :: v) := v.

Equations vec_vec {A:Type} {n} (v : vec  A n) : vec A n :=
vec_vec _ (n:=0) := [];
vec_vec v := (head v) :: (tail v).
