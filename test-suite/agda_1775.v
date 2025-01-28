From Equations.Prop Require Import Equations.

From Stdlib Require Import Utf8.
(* Set Universe Polymorphism. *)
(** Can we define NoConfusion in SProp (squashing equalities of arguments)?
    Would not allow to show equivalence to (x = y) for non-strict sets. *)

Import Sigma_Notations.
Open Scope equations_scope.

Inductive fin : nat -> Set :=
| fin0 n : fin (S n)
| finS n : fin n -> fin (S n).
Derive Signature NoConfusion for fin.

Arguments fin0 {_}.
Arguments finS {_} _.

(* Derive NoConfusion for ℕ. *)
Derive NoConfusionHom for fin.

Inductive Vec (A : Set) : nat -> Set :=
  nil  : Vec A O
| cons : forall {n} (x : A) (xs : Vec A n), Vec A (S n).

Derive Signature NoConfusion NoConfusionHom for Vec.
Arguments nil {_}.
Arguments cons {_} _ _.

Reserved Notation " x [ f ]= y " (at level 0, no associativity, f at next level, y at next level).
Inductive at_eq {A : Set} : forall{n : nat}, Vec A n -> fin n -> A -> Set :=
| here  : ∀ {n}     {x}   {xs : Vec A n}, at_eq (cons _ x xs) fin0 x
| there : ∀ {n} {i : fin n} {x y} {xs : Vec A n} (H : xs [ i ]= x),
    (cons _ y xs) [ (finS i) ]= x
where " x [ n ]= y " := (at_eq x n y).

Derive Signature for at_eq.

Definition Subset := Vec bool.

Reserved Notation " x ∈ S " (at level 4).

Definition inS {n} (f : fin n) (s : Subset n) := s [ f ]= true.
Notation "x ∈ S" := (inS x S).

Equations drop_there {s n x} {p : Subset n} (H : (finS x) ∈ (cons _ s p)) : x ∈ p :=
  drop_there (there l) := l.

Inductive Dec (P : Set) : Set :=
| yes ( p :   P) : Dec P
| no ( p : P -> False) : Dec P.
Arguments yes {_} _.
Arguments no {_} _.

Equations? isin {n} (x : fin n) (p : Subset n) : Dec (x ∈ p) :=
isin fin0 (cons true p) := yes here;
isin fin0 (cons false p) := no _;
isin (finS f) (cons s p) with isin f p :=
                             | yes H := yes (there H);
                             | no H := no (fun H' => _).
Proof. depelim H. depelim H'. apply (H H'). Defined.
Transparent isin.

Print Assumptions isin.