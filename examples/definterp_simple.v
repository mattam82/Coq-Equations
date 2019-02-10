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

Section MapAll.
  Context  {A} {P Q : A -> Type} (f : forall x, P x -> Q x).

  Equations map_all {l : list A} : All P l -> All Q l :=
  map_all all_nil := all_nil;
  map_all (all_cons p ps) := all_cons (f _ p) (map_all ps).
End MapAll.

Inductive Val : Ty -> Set :=
| val_unit : Val unit
| val_closure {Γ t u} : Expr (t :: Γ) u -> All Val Γ -> Val (t ⇒ u).

Derive Signature NoConfusion NoConfusionHom for Val.

Definition Env (Γ : Ctx) : Set := All Val Γ.

Equations lookup : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x :=
  lookup (all_cons p _) here := p;
  lookup (all_cons _ ps) (there ins) := lookup ps ins.

Equations update : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x -> All P xs :=
  update (all_cons p ps) here        p' := all_cons p' ps;
  update (all_cons p ps) (there ins) p' := all_cons p (update ps ins p').

Equations M : Ctx -> Type -> Type :=
  M Γ A := Env Γ -> option A.

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

Equations eval : ∀ (n : nat) {Γ t} (e : Expr Γ t), M Γ (Val t) :=
  eval 0 _             := timeout;
  eval (S k) tt        := ret val_unit;
  eval (S k) (var x)   := getEnv >>= fun E => ret (lookup E x);
  eval (S k) (abs x)   := getEnv >>= fun E => ret (val_closure x E);
  eval (S k) (app (Γ:=Γ) f arg) := eval k f >>= (#{ | val_closure e' E =>
                                               eval k arg >>= fun a' => usingEnv (all_cons a' E) (eval k e')}).

Inductive eval_sem {Γ : Ctx} {env : Env Γ} : forall {t : Ty}, Expr Γ t -> Val t -> Prop :=
| eval_tt (e : Expr Γ unit) : eval_sem e val_unit
| eval_var t (i : t ∈ Γ) : eval_sem (var i) (lookup env i)
| eval_abs {t u} (b : Expr (t :: Γ) u) : eval_sem (abs b) (val_closure b env)
| eval_app {t u} (f : Expr Γ (t ⇒ u)) b' (a : Expr Γ t) v :
    eval_sem f (val_closure b' env) ->
    eval_sem a v ->
    forall u, @eval_sem (t :: Γ) (all_cons v env) _ b' u ->
    eval_sem (app f a) u.



Lemma eval_correct {n} Γ t (e : Expr Γ t) env v : eval n e env = Some v -> @eval_sem _ env _ e v.
Proof.
  pose proof (fun_elim (f:=eval)).
  specialize (H (fun n Γ t e m => forall env v, m env = Some v -> @eval_sem _ env _ e v)
                (fun n Γ t u f a v m => forall env v',
                     @eval_sem _ env _ f v -> m env = Some v' -> @eval_sem _ env _ (app f a) v')).
  rapply H; clear; intros.
  discriminate.
  noconf H. constructor.
  noconf H. constructor.

  noconf H. constructor.

  unfold bind in H1.
  destruct (eval n e0 env) eqn:Heq.
  specialize (H _ _ Heq).
  specialize (H0 v0 _ _ H H1). apply H0.
  discriminate.

  (* Context mismatch *)
  unfold bind in H2.
  destruct (eval k arg env) eqn:Heq.
  specialize (H _ _ Heq).
  unfold usingEnv in H2. specialize (H0 v (all_cons v a) v').
  econstructor; eauto.
Admitted.