From Equations Require Import Equations DepElimDec HSets.
Set Universe Polymorphism.

Inductive ℕ (E:Set) : Set :=
| O : ℕ E
| S : ℕ E -> ℕ E
| raise : E -> ℕ E.

Arguments O {_}.
Arguments S {_} _.

Inductive Vec E (A : Set) : ℕ E -> Set :=
  nil  : Vec E A O
| cons : forall {n} (x : A) (xs : Vec E A n), Vec E A (S n).

Arguments nil {_ _}.
Arguments cons {_ _ _} _ _.

Inductive vector_param E (A : Set) : forall (n : ℕ E), Vec E A n -> Set :=
  vnil_param : vector_param E A O nil
| vcons_param : forall (n : ℕ E) (a : A) (v : Vec E A n),
                  vector_param E A n v ->
                  vector_param E A (S n) (cons a v).
Derive Signature for vector_param.

Derive NoConfusion for ℕ.
Derive NoConfusion for Vec.
Derive NoConfusion for vector_param.
Derive NoConfusionHom for Vec.
Derive NoConfusionHom for vector_param.

Import Sigma_Notations.
Open Scope equations_scope.

Equations param_vector_vcons E (A : Set) (a : A) (n : ℕ E) (v : Vec E A n)
          (X : vector_param E A (S n) (cons a v)) : vector_param E A n v :=
  param_vector_vcons E A _ _ _  (vcons_param _ _ _ X) := X.
