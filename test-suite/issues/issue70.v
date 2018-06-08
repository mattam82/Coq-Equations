From Coq Require Import Fin.
From Equations Require Import Equations.
Set Equations Transparent.

Equations FL (n : nat) : Fin.t (S n) :=
  FL 0     := F1;
  FL (S n) := FS (FL n).

Equations FU {n : nat} (x : Fin.t n) : Fin.t (S n) :=
  FU F1     := F1;
  FU (FS x) := FS (FU x).

Equations invertFin {n : nat} (x : Fin.t n) : Fin.t n :=
  invertFin  F1    := FL _;
  invertFin (FS x) := FU (invertFin x).

Equations invFULemma {n : nat} (x : Fin.t n) :
                     invertFin (FU x) = FS (invertFin x) :=
  invFULemma F1     := _;
  invFULemma (FS x) := (f_equal _ (invFULemma x)).

Equations invFLLemma (n : nat) : invertFin (FL n) = F1 :=
  invFLLemma 0     := eq_refl;
  invFLLemma (S n) := (f_equal _ (invFLLemma n)).

Equations invertFinInv {n : nat} (x : Fin.t n) :
                       invertFin (invertFin x) = x :=
  invertFinInv {n:=0}      x     :=! x;
  invertFinInv {n:=(S _)}  F1    := (invFLLemma _);
  invertFinInv {n:=(S _)} (FS y) := (eq_trans
                                     (invFULemma (invertFin y))
                                     (f_equal _ (invertFinInv y))).

Definition invFinViewType {n : nat} (x : (Fin.t n)) : Type :=
  { y : Fin.t n & x = invertFin y }.

Definition invFinView {n : nat} (x : (Fin.t n)) : invFinViewType x :=
  existT _ (invertFin x) (eq_sym (invertFinInv x)).

Equations finFUOrFL {n : nat} (x : Fin.t (S n)) :
                    { y : Fin.t n & x = FU y } + ( x = FL n ) :=
  finFUOrFL  {n:=0}     F1                     := (inr eq_refl);
  finFUOrFL  {n:=(S _)} x <= invFinView x => {
                          | (existT F1 eq)     := (inr eq);
                          | (existT (FS _) eq) := (inl (existT _ (invertFin _) eq))}.