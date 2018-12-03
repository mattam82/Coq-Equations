Require Import Program.Basics Program.Tactics.
Require Import Equations.Equations.
Require Import Coq.Vectors.VectorDef.
Require Import List.
Import ListNotations.
Set Equations Transparent.

Derive Signature NoConfusion NoConfusionHom for t.

Inductive Ty : Set :=
| unit : Ty
| arrow (t u : Ty) : Ty.

Derive NoConfusion for Ty.

Infix "⇒" := arrow (at level 80).

Definition Ctx := list Ty.

Reserved Notation " x ∈ s " (at level 70, s at level 10).

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).

Arguments here {A x xs}.
Arguments there {A x y xs} _.

Inductive Expr : Ctx -> Ty -> Set :=
| tt {Γ} : Expr Γ unit
| var {Γ} {t} : In t Γ -> Expr Γ t
| abs {Γ} {t u} : Expr (t :: Γ) u -> Expr Γ (t ⇒ u)
| app {Γ} {t u} : Expr Γ (t ⇒ u) -> Expr Γ t -> Expr Γ u.

Derive Signature NoConfusion NoConfusionHom for Expr.

Inductive All {A} (P : A -> Type) : list A -> Type :=
| all_nil : All P []
| all_cons {x xs} : P x -> All P xs -> All P (x :: xs).
Arguments all_nil {A} {P}.
Arguments all_cons {A P x xs} _ _.
Derive Signature NoConfusion NoConfusionHom for All.

Inductive Val : Ty -> Set :=
| val_unit : Val unit
| val_closure {Γ t u} : Expr (t :: Γ) u -> All Val Γ -> Val (t ⇒ u).
Derive Signature NoConfusion NoConfusionHom for Val.

Definition Env : Ctx -> Set := All Val.

Equations lookup : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x :=
  lookup (all_cons p _) here := p;
  lookup (all_cons _ ps) (there ins) := lookup ps ins.

Equations M : Ctx -> Type -> Type :=
  M Γ τ := Env Γ -> option τ.

Require Import Utf8.

Equations bind : ∀ {Γ A B}, M Γ A → (A → M Γ B) → M Γ B :=
  bind m f γ := match m γ with
              | None => None
              | Some x => f x γ
              end.
Infix ">>=" := bind (at level 20, left associativity).

Equations ret : ∀ {Γ A}, A → M Γ A :=
  ret a γ := Some a.

Equations getEnv : ∀ {Γ}, M Γ (Env Γ) :=
  getEnv γ := Some γ.

Equations usingEnv : ∀ {Γ Γ' A}, Env Γ → M Γ A → M Γ' A :=
  usingEnv γ m γ' := m γ.

Equations timeout : ∀ {Γ A}, M Γ A :=
  timeout _ := None.


Equations foo (n : nat) : nat :=
foo n := n + k 0

  where k (x : nat) : nat :=
  { k 0 := 0;
    k (S n) := n }.
Next Obligation. destruct n; simp foo. Defined.
(** This pattern matching lambda does not capture the scope (e, E, a') but builds it, still it fails *)
Axiom cheat : forall{A}, A.

Section Foo.
  Variable t' u' : Ty.
  Variable Γ : Ctx.

  Equations closure_inv (v : Val (t' ⇒ u')) (a : Val t') : M Γ (Val u') :=
    closure_inv (val_closure e E) a := cheat.
End Foo.

(* Equations(noind) eval : nat → ∀ {Γ t}, Expr Γ t → M Γ (Val t) := *)
(*   eval 0 _             := timeout; *)
(*   eval (S k) tt        := ret val_unit; *)
(*   eval (S k) (var x)   := getEnv >>= fun E => ret (lookup E x); *)
(*   eval (S k) (abs x)   := getEnv >>= fun E => ret (val_closure x E); *)
(*   eval (S k) (app f arg) := *)
(*     eval k f >>= (#{ | val_closure e' E => *)
(*                        eval k arg >>= fun a' => usingEnv (all_cons a' E) (eval k e') }). *)

Equations(noeqns noind) eval : nat → ∀ {Γ t}, Expr Γ t → M Γ (Val t) :=
  eval 0 _             := timeout;
  eval (S k) tt        := ret val_unit;
  eval (S k) (var x)   := getEnv >>= fun E => ret (lookup E x);
  eval (S k) (abs x)   := getEnv >>= fun E => ret (val_closure x E);
  eval (S k) (app f arg) := eval k f >>= (#{ | val_closure e' E =>
                                               eval k arg >>= fun a' => usingEnv (all_cons a' E) (eval k e')}).
