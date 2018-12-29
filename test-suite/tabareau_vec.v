From Equations Require Import Equations DepElimDec HSets.
Set Universe Polymorphism.

Inductive ℕ (E:Set) : Set :=
| O : ℕ E
| S : ℕ E -> ℕ E
| raise : E -> ℕ E.
Derive NoConfusion for ℕ.

Arguments O {_}.
Arguments S {_} _.

Inductive Vec E (A : Set) : ℕ E -> Set :=
  nil  : Vec E A O
| cons : forall {n} (x : A) (xs : Vec E A n), Vec E A (S n).
Derive Signature NoConfusion NoConfusionHom for Vec.

Arguments nil {_ _}.
Arguments cons {_ _ _} _ _.

Inductive vector_param E (A : Set) : forall (n : ℕ E), Vec E A n -> Set :=
  vnil_param : vector_param E A O nil
| vcons_param : forall (n : ℕ E) (a : A) (v : Vec E A n),
                  vector_param E A n v ->
                  vector_param E A (S n) (cons a v).
Derive Signature NoConfusion NoConfusionHom for vector_param.

Equations param_vector_vcons E (A : Set) (a : A) (n : ℕ E) (v : Vec E A n)
          (X : vector_param E A (S n) (cons a v)) : vector_param E A n v :=
  param_vector_vcons E A _ _ _  (vcons_param _ _ _ X) := X.

Definition foo := param_vector_vcons_elim :
  forall
    P : forall (E A : Set) (a : A) (n : ℕ E) (v : Vec E A n),
      vector_param E A (S n) (cons a v) -> vector_param E A n v -> Prop,

    (forall (E A : Set) (a0 : A) (n0 : ℕ E) (v0 : Vec E A n0) (v1 : vector_param E A n0 v0),
        P E A a0 n0 v0 (vcons_param E A n0 a0 v0 v1) v1) ->

    forall (E A : Set) (a : A) (n : ℕ E) (v : Vec E A n) (X : vector_param E A (S n) (cons a v)),
      P E A a n v X (param_vector_vcons E A a n v X).

(* Print Assumptions param_vector_vcons. *)
