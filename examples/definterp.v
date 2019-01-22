(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(* end hide *)
(** * Definitional interpreter for STLC extended with references

  This is a port of the first part of "Intrinsically-Typed Definitional
  Interpreters for Imperative Languages", Poulsen, Rouvoet, Tolmach,
  Krebbers and Visser. POPL'18.

  It uses well-typed and well-scoped syntax and an indexed monad to
  define an interpreter for an imperative programming language.

  This showcases the use of dependent pattern-matching and pattern-matching
  lambdas in Equations. We implement a variant where store extension is
  resolved using type class resolution as well as the dependent-passing
  style version. *)

Require Import Program.Basics Program.Tactics.
From Equations Require Import Equations.
Require Import Coq.Vectors.VectorDef.
Require Import List.
Import ListNotations.
Set Equations Transparent.

(** [t] is just [Vector.t] here. *)
Derive Signature NoConfusion NoConfusionHom for t.

(** Types include unit, bool, function types and references *)
Inductive Ty : Set :=
| unit : Ty
| bool : Ty
| arrow (t u : Ty) : Ty
| ref : Ty -> Ty.

Derive NoConfusion for Ty.

Infix "⇒" := arrow (at level 80).

Definition Ctx := list Ty.

Reserved Notation " x ∈ s " (at level 70, s at level 10).

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).
Derive Signature NoConfusion for In.

Arguments here {A x xs}.
Arguments there {A x y xs} _.

Inductive Expr : Ctx -> Ty -> Set :=
| tt {Γ} : Expr Γ unit
| true {Γ} : Expr Γ bool
| false {Γ} : Expr Γ bool
| ite {Γ t} : Expr Γ bool -> Expr Γ t -> Expr Γ t -> Expr Γ t
| var {Γ} {t} : In t Γ -> Expr Γ t
| abs {Γ} {t u} : Expr (t :: Γ) u -> Expr Γ (t ⇒ u)
| app {Γ} {t u} : Expr Γ (t ⇒ u) -> Expr Γ t -> Expr Γ u
| new {Γ t} : Expr Γ t -> Expr Γ (ref t)
| deref {Γ t} : Expr Γ (ref t) -> Expr Γ t
| assign {Γ t} : Expr Γ (ref t) -> Expr Γ t -> Expr Γ unit.

(** We derive both [NoConfusion] and [NoConfusionHom] principles here, the later
    allows to simplify pattern-matching problems on [Expr] which would otherwise
    require K. It relies on an inversion analysis of every constructor, showing
    that the context and type indexes in the conclusions of every constructor
    are forced arguments. *)
Derive Signature NoConfusion NoConfusionHom for Expr.

Inductive All {A} (P : A -> Type) : list A -> Type :=
| all_nil : All P []
| all_cons {x xs} : P x -> All P xs -> All P (x :: xs).
Arguments all_nil {A} {P}.
Arguments all_cons {A P x xs} _ _.
Derive Signature NoConfusion NoConfusionHom for All.

Section MapAll.
  Context {A} {P Q : A -> Type} (f : forall x, P x -> Q x).

  Equations map_all {l : list A} : All P l -> All Q l :=
  map_all all_nil := all_nil;
  map_all (all_cons p ps) := all_cons (f _ p) (map_all ps).

  Equations map_all_in {l : list A} (f : forall x, x ∈ l -> P x -> Q x) : All P l -> All Q l :=
  map_all_in f all_nil := all_nil;
  map_all_in f (all_cons p ps) := all_cons (f _ here p) (map_all_in (fun x inl => f x (there inl)) ps).
End MapAll.

Section AllSize.
  Context {A} (P : A -> Type) (size : forall {x : A}, P x -> nat).

  Equations all_size {l : list A} : All P l -> nat :=
  all_size all_nil := 0;
  all_size (all_cons p ps) := size _ p + all_size ps.
End AllSize.

Definition StoreTy := list Ty.

Inductive Val : Ty -> StoreTy -> Set :=
| val_unit {Σ} : Val unit Σ
| val_true {Σ} : Val bool Σ
| val_false {Σ} : Val bool Σ
| val_closure {Σ Γ t u} : Expr (t :: Γ) u -> All (fun t => Val t Σ) Γ -> Val (t ⇒ u) Σ
| val_loc {Σ t} : t ∈ Σ -> Val (ref t) Σ.

Derive Signature NoConfusion NoConfusionHom for Val.

Definition Env (Γ : Ctx) (Σ : StoreTy) : Set := All (fun t => Val t Σ) Γ.

Definition Store (Σ : StoreTy) := All (fun t => Val t Σ) Σ.

Equations lookup : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x :=
  lookup (all_cons p _) here := p;
  lookup (all_cons _ ps) (there ins) := lookup ps ins.

Equations update : forall {A P xs} {x : A}, All P xs -> x ∈ xs -> P x -> All P xs :=
  update (all_cons p ps) here        p' := all_cons p' ps;
  update (all_cons p ps) (there ins) p' := all_cons p (update ps ins p').

Equations lookup_store {Σ t} : t ∈ Σ -> Store Σ -> Val t Σ :=
  lookup_store l σ := lookup σ l.

Equations update_store {Σ t} : t ∈ Σ -> Val t Σ -> Store Σ -> Store Σ :=
  update_store l v σ := update σ l v.
Import Sigma_Notations.

Definition store_incl (Σ Σ' : StoreTy) := &{ Σ'' : _ & Σ' = Σ'' ++ Σ }.
Infix "⊑" := store_incl (at level 10).

Lemma app_assoc {A} (x y z : list A) : x ++ y ++ z = (x ++ y) ++ z.
Proof. induction x; simpl; auto.
       now rewrite IHx.
Defined.

Section StoreIncl.
  Context {Σ Σ' : StoreTy} (incl : Σ ⊑ Σ').

  Lemma pres_in t : t ∈ Σ -> t ∈ Σ'.
  Proof. destruct incl. subst. clear. induction pr1. intros. exact H.
         intros H. specialize (IHpr1 H). constructor 2. apply IHpr1.
  Defined.

  Equations weaken_val {t} (v : Val t Σ) : Val t Σ' := {
   weaken_val (@val_unit ?(Σ)) := val_unit;
   weaken_val val_true := val_true;
   weaken_val val_false := val_false;
   weaken_val (val_closure b e) := val_closure b (weaken_vals e);
   weaken_val (val_loc H) := val_loc (pres_in _ H) }
  where weaken_vals {l} (a : All (fun t => Val t Σ) l) : All (fun t => Val t Σ') l :=
  weaken_vals all_nil := all_nil;
  weaken_vals (all_cons p ps) := all_cons (weaken_val p) (weaken_vals ps).

  Lemma weakenv_vals {l} a : @weaken_vals l a = map_all (fun t v => weaken_val v) a.
  Proof. induction a; simpl; reflexivity. Defined.

  Definition weaken_env {Γ} (v : Env Γ Σ) : Env Γ Σ' :=
    map_all (@weaken_val) v.

  Lemma refl_incl : Σ ⊑ Σ.
  Proof. exists []. reflexivity. Defined.

  Lemma trans_incl {Σ''} (incl' : Σ' ⊑ Σ'') : Σ ⊑ Σ''.
  Proof.
    destruct incl as [? ->], incl' as [? ->].
    exists (pr0 ++ pr1). now rewrite app_assoc.
  Defined.

  Lemma store_ext_incl {t} : Σ ⊑ (t :: Σ).
  Proof. now exists [t]. Defined.

End StoreIncl.

Infix "⊚" := trans_incl (at level 10).

Equations M : forall (Γ : Ctx) (P : StoreTy -> Type) (Σ : StoreTy), Type :=
  M Γ P Σ := forall (E : Env Γ Σ) (μ : Store Σ), option &{ Σ' : _ & &{ _ : Store Σ' & &{ _ : P Σ' & Σ ⊑ Σ'}}}.

Require Import Utf8.
Notation "( x , .. , y , z )" := (sigmaI _ x .. (sigmaI _ y z) ..) : core_scope.

Equations bind {Σ Γ} {P Q : StoreTy -> Type} (f : M Γ P Σ) (g : ∀ {Σ'}, P Σ' -> M Γ Q Σ') : M Γ Q Σ :=
  bind f g E μ with f E μ :=
    { | None := None;
      | Some (Σ', μ', x, ext) with g _ x (weaken_env ext E) μ' :=
          { | None := None;
            | Some (_, μ'', y, ext') := Some (_, μ'', y, ext ⊚ ext') } }.

Infix ">>=" := bind (at level 20, left associativity).

Definition transp_op {Γ Σ P} (x : Store Σ -> P Σ) : M Γ P Σ :=
  fun E μ => Some (Σ, μ, x μ, refl_incl).

Equations ret : ∀ {Γ Σ P}, P Σ → M Γ P Σ :=
  ret (Σ:=Σ) a E μ := Some (Σ, μ, a, refl_incl).

Equations getEnv : ∀ {Γ Σ}, M Γ (Env Γ) Σ :=
  getEnv (Σ:=Σ) E μ := Some (Σ, μ, E, refl_incl).

Equations usingEnv {Γ Γ' Σ P} (E : Env Γ Σ) (m : M Γ P Σ) : M Γ' P Σ :=
  usingEnv E m E' μ := m E μ.

Equations timeout : ∀ {Γ Σ P}, M Γ P Σ :=
  timeout _ _ := None.

Section StoreOps.
  Context {Σ : StoreTy} {Γ : Ctx} {t : Ty}.

  Equations storeM (v : Val t Σ) : M Γ (Val (ref t)) Σ :=
    storeM v E μ :=
      let v : Val t (t :: Σ) := weaken_val store_ext_incl v in
      let μ' := map_all (fun t' => weaken_val store_ext_incl) μ in
      Some (t :: Σ, all_cons v μ', val_loc here, store_ext_incl).

  Equations derefM (l : t ∈ Σ) : M Γ (Val t) Σ :=
    derefM l := transp_op (lookup_store l).

  Equations updateM (l : t ∈ Σ) (v : Val t Σ) : M Γ (Val unit) Σ :=
    updateM l v E μ := Some (Σ, update_store l v μ, val_unit, refl_incl).
End StoreOps.

Reserved Notation "P ⊛ Q" (at level 10).

Inductive storepred_prod (P Q : StoreTy -> Type) : StoreTy -> Type :=
  | storepred_pair {Σ} : P Σ -> Q Σ -> (P ⊛ Q) Σ
where "P ⊛ Q" := (storepred_prod P Q).
Arguments storepred_pair {P Q Σ}.

Class Weakenable (P : StoreTy -> Type) : Type :=
  weaken : forall {Σ Σ'}, Σ ⊑ Σ' -> P Σ -> P Σ'.

Instance val_weaken {t} : Weakenable (Val t).
Proof. intros Σ Σ' incl. apply (weaken_val incl). Defined.

Instance env_weaken {Γ} : Weakenable (Env Γ).
Proof. intros Σ Σ' incl. apply (weaken_env incl). Defined.

Instance loc_weaken (t : Ty) : Weakenable (In t).
Proof. intros Σ Σ' incl. apply (pres_in incl). Defined.

Class IsIncludedOnce (Σ Σ' : StoreTy) : Type := is_included_once : Σ ⊑ Σ'.
Hint Mode IsIncludedOnce + + : typeclass_instances.

Instance IsIncludedOnce_ext {T} Σ : IsIncludedOnce Σ (T :: Σ).
Proof. apply store_ext_incl. Defined.

Class IsIncluded (Σ Σ' : StoreTy) : Type := is_included : Σ ⊑ Σ'.
Hint Mode IsIncluded + + : typeclass_instances.

Instance IsIncluded_refl Σ : IsIncluded Σ Σ := refl_incl.
Instance IsIncluded_trans Σ Σ' Σ'' : IsIncludedOnce Σ Σ' -> IsIncluded Σ' Σ'' -> IsIncluded Σ Σ''.
Proof. intros H H'. exact (trans_incl H H'). Defined.

Equations wk {Σ Σ' P} {W : Weakenable P} (p : P Σ) {incl : IsIncluded Σ Σ'} : P Σ' :=
  wk p := weaken incl p.

Equations bind_ext {Σ Γ} {P Q : StoreTy -> Type} (f : M Γ P Σ) (g : ∀ {Σ'} `{IsIncluded Σ Σ'}, P Σ' -> M Γ Q Σ') : M Γ Q Σ :=
  bind_ext f g E μ with f E μ :=
    { | None := None;
      | Some (Σ', μ', x, ext) with g _ ext x (weaken_env ext E) μ' :=
          { | None := None;
            | Some (_, μ'', y, ext') := Some (_, μ'', y, ext ⊚ ext') } }.

Infix ">>='" := bind_ext (at level 20, left associativity).

Equations eval_ext (n : nat) {Γ Σ t} (e : Expr Γ t) : M Γ (Val t) Σ :=
  eval_ext 0 _                := timeout;
  eval_ext (S k) tt           := ret val_unit;
  eval_ext (S k) true         := ret val_true;
  eval_ext (S k) false        := ret val_false;
  eval_ext (S k) (ite b t f)  := eval_ext k b >>=' λ{ | _ | ext | val_true => eval_ext k t;
                                                      | _ | ext | val_false => eval_ext k f };

  eval_ext (S k) (var x)      := getEnv >>=' fun {Σ ext} E => ret (lookup E x);
  eval_ext (S k) (abs x)      := getEnv >>=' fun {Σ ext} E => ret (val_closure x E);
  eval_ext (S k) (app (Γ:=Γ) e1 e2) :=
      eval_ext k e1 >>=' λ{ | _ | ext | val_closure e' E => 
      eval_ext k e2 >>=' fun {Σ' ext'} v => usingEnv (all_cons v (wk E)) (eval_ext k e')};
  eval_ext (S k) (new e)      := eval_ext k e >>=' fun {Σ ext} v => storeM v;
  eval_ext (S k) (deref l)    := eval_ext k l >>=' λ{ | _ | ext | val_loc l => derefM l };
  eval_ext (S k) (assign l e) := eval_ext k l >>=' λ{ | _ | ext | val_loc l =>
                                 eval_ext k e >>=' λ{ | _ | ext | v => updateM (wk l) (wk v) }}.

Equations strength {Σ Γ} {P Q : StoreTy -> Type} {w : Weakenable Q} (m : M Γ P Σ) (q : Q Σ) : M Γ (P ⊛ Q) Σ :=
  strength m q E μ with m E μ => {
    | None => None;
    | Some (Σ, μ', p, ext) => Some (Σ, μ', storepred_pair p (weaken ext q), ext) }.

Infix "^" := strength.

(* Issue: improve pattern matching lambda to have implicit arguments implicit.
   Hard because Coq does not keep the implicit status of bind's [g] argument. *)

Equations eval (n : nat) {Γ Σ t} (e : Expr Γ t) : M Γ (Val t) Σ :=
  eval 0 _                := timeout;
  eval (S k) tt           := ret val_unit;
  eval (S k) true         := ret val_true;
  eval (S k) false        := ret val_false;
  eval (S k) (ite b t f)  := eval k b >>= λ{ | _ | val_true => eval k t;
                                             | _ | val_false => eval k f };

  eval (S k) (var x)      := getEnv >>= fun Σ E => ret (lookup E x);
  eval (S k) (abs x)      := getEnv >>= fun Σ E => ret (val_closure x E);
  eval (S k) (app (Γ:=Γ) e1 e2) :=
      eval k e1 >>= λ{ | _ | val_closure e' E =>
                             (eval k e2 ^ E) >>= fun Σ' '(storepred_pair v E) => usingEnv (all_cons v E) (eval k e')};
  eval (S k) (new e)      := eval k e >>= fun Σ v => storeM v;
  eval (S k) (deref l)    := eval k l >>= λ{ | _ | val_loc l => derefM l };
  eval (S k) (assign l e) := eval k l >>= λ{ | _ | val_loc l =>
                             (eval k e ^ l) >>= λ{ | _ | storepred_pair v l => updateM l v }}.

Definition idu : Expr [] (unit ⇒ unit) :=
  abs (var here).

Definition idapp : Expr [] unit := app idu tt.

(** All definitions are axiom-free (and actually not even dependent on a provable UIP instance), so
 everything computes. *)
Eval vm_compute in eval 100 idapp all_nil all_nil.

Definition neg : Expr [] (bool ⇒ bool) :=
  abs (ite (var here) false true).

Definition letref {t u} (v : Expr [] t) (b : Expr [ref t] u) : Expr [] u :=
  app (abs b) (new v).

(** [Equations?] enters refinement mode, which can be used to solve the case of variables in proof mode. *)
Equations? weaken_expr {Γ Γ' t u} (e1 : Expr (Γ ++ Γ') t) : Expr (Γ ++ u :: Γ') t :=
  weaken_expr tt              := tt;
  weaken_expr true            := true;
  weaken_expr false           := false;
  weaken_expr (ite b t f)     := ite (weaken_expr b) (weaken_expr t) (weaken_expr f);
  weaken_expr (var (t:=ty) x) := var _;
  weaken_expr (abs (t:=t) x)  := abs (weaken_expr (Γ := t :: Γ) x);
  weaken_expr (app e1 e2)     := app (weaken_expr e1) (weaken_expr e2);
  weaken_expr (new e)         := new (weaken_expr e);
  weaken_expr (deref l)       := deref (weaken_expr l);
  weaken_expr (assign l e)    := assign (weaken_expr l) (weaken_expr e).
Proof.
  clear weaken_expr.
  induction Γ in Γ', u, x |- *. now apply there. simpl.
  depelim x. constructor. apply there. apply IHΓ. apply x.
Defined.

Definition seq {Γ u} (e1 : Expr Γ unit) (e2 : Expr Γ u) : Expr Γ u :=
  app (abs (weaken_expr (Γ := []) e2)) e1.

(* let x = ref true in
   x := false; !x *)

Definition letupdate : Expr [] bool :=
  letref true (seq (assign (var here) false) (deref (var here))).

Eval vm_compute in eval 100 letupdate all_nil all_nil.
