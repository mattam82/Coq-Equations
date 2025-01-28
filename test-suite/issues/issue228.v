From Coq Require Import Utf8.
From Coq Require Import Equality.
From Coq Require Import Arith.
From Coq Require Vector.
Import Vector.VectorNotations.
From Equations.Prop Require Import Equations.

Inductive MType : Type :=
| Base : Set → MType
| Channel : SType → MType

with SType : Type :=
| ø : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
| Branch: ∀ {n}, Vector.t SType n → SType
| Select : ∀ {n}, Vector.t SType n → SType
.

Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity).
Notation "? m ; s" := (Receive m s) (at level 90, right associativity).
Notation "▹ ss" := (Branch ss) (at level 90, right associativity).
Notation "◃ ss" := (Select ss) (at level 90, right associativity).

Inductive Duality : SType → SType → Prop :=
| Ends : Duality ø ø
| MRight : ∀ {m c₁ c₂}, Duality c₁ c₂ → Duality (Send m c₁) (Receive m c₂)
| MLeft : ∀ {m c₁ c₂}, Duality c₁ c₂ → Duality (Receive m c₁) (Send m c₂)
.

Section Processes.
  Variable ST : Type.
  Variable MT : Type → Type.

  Inductive Message : MType → Type :=
  | V : ∀ {M : Set}, MT M → Message (Base M)
  | C : ∀ {S : SType}, ST → Message (Channel S)
  .

  Arguments V [M].
  Arguments C [S].

  Inductive Process : Type :=
  | PSelect
    : ∀ {n : nat} {ss : Vector.t SType n}
    (i : Fin.t n)
    , Message C[Select ss]
    → (Message C[ss[@i]] → Process)
    → Process
  .
  
End Processes.

(**************************)
(*        NICETIES        *)
(**************************)

Arguments V [ST MT M].
Arguments C [ST MT S].
Arguments PSelect [ST MT n ss].

(**************************)
(*       LINEARITY        *)
(**************************)

Definition TMT : Type → Type := fun _ => unit.

Derive NoConfusion for MType.
Derive Signature NoConfusionHom for Message.

(* t means "Has it been already found?" *)

Equations find (t : bool) (p : Process bool TMT) : Prop by struct p :=
find t (PSelect i (C c) p) => find t (p (C false))
.

