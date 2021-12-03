From Equations Require Import Equations.

Notation Π A B := (forall (a : A), B a).
Definition Πpred {A B} PA PB (f : Π A B) :=
  forall a (aϵ : PA a), PB a aϵ (f a).

Inductive valid1 : forall (A : Type) (R : A -> Type), Type :=
| Vpi1 {A B PA PB} :
    valid1 A PA ->
    (forall a (aϵ : PA a), valid1 (B a) (PB a aϵ)) ->
    valid1 (Π A B) (Πpred PA PB).

Obligation Tactic := idtac.
Derive NoConfusion for valid1.
(* Instant !*)
Print noConfusion_valid1_obligation_1.

Definition Πrel {A A' B B'} RA RB (f : Π A B) (f' : Π A' B') :=
  forall a a' (aa' : RA a a'), RB a a' aa' (f a) (f' a').

Inductive valid2 : forall (A : Type) (B : Type) (R : A -> B -> Type), Type :=
| Vpi2 {A A' B B' RA RB} :
    valid2 A A' RA ->
    (forall a a' (aa' : RA a a'), valid2 (B a) (B' a') (RB a a' aa')) ->
    valid2 (Π A B) (Π A' B') (Πrel RA RB).

Obligation Tactic := idtac.
Derive NoConfusion for valid2.

Inductive code : Type -> Type :=
| Cpi {A B} (Ac : code A) (Bc : forall a : A, code (B a)) : code (forall a, B a).

Inductive valid : forall (A : Type) (Ac : code A) (B : Type) (Bc : code B)
                    (R : A -> B -> Type), Type :=
| Vpi {A Ac A' Ac' B Bc B' Bc' RA RB} :
    valid A Ac A' Ac' RA ->
    (forall a a' (aa' : RA a a'), valid (B a) (Bc a) (B' a') (Bc' a') (RB a a' aa')) ->
    valid (Π A B) (Cpi Ac Bc) (Π A' B') (Cpi Ac' Bc') (Πrel RA RB).

Obligation Tactic := idtac.
Timeout 3 Derive NoConfusion for valid.
