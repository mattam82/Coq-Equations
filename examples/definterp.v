Require Import Program.Basics Program.Tactics.
Require Import Equations.Equations.
Require Import Coq.Vectors.VectorDef.
Require Import List.
Import ListNotations.
Set Equations Transparent.

Derive Signature NoConfusion NoConfusionHom for t.

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

  Equations(noind) weaken_val {t} (v : Val t Σ) : Val t Σ' :=
   weaken_val val_unit := val_unit;
   weaken_val val_true := val_true;
   weaken_val val_false := val_false;
   weaken_val (val_closure b e) := val_closure b (map_all (fun t v => weaken_val v) e);
   weaken_val (val_loc H) := val_loc (pres_in _ H).

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
(* TODO improve pattern matching lambda to have implicit arguments implicit.
   Hard because Coq does not keep the implicit status of bind's [g] argument. *)

Equations(noind) eval (n : nat) {Γ Σ t} (e : Expr Γ t) : M Γ (Val t) Σ :=
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

Eval vm_compute in eval 100 idapp all_nil all_nil.

Definition neg : Expr [] (bool ⇒ bool) :=
  abs (ite (var here) false true).

Definition letref {t u} (v : Expr [] t) (b : Expr [ref t] u) : Expr [] u :=
  app (abs b) (new v).

Equations weaken_expr {Γ Γ' t u} (e1 : Expr (Γ ++ Γ') t) : Expr (Γ ++ u :: Γ') t :=
  weaken_expr tt             := tt;
  weaken_expr true           := true;
  weaken_expr false          := false;
  weaken_expr (ite b t f)    := ite (weaken_expr b) (weaken_expr t) (weaken_expr f);
  weaken_expr (var x)        := var _;
  weaken_expr (abs (t:=t) x) := abs (weaken_expr (Γ := t :: Γ) x);
  weaken_expr (app e1 e2)    := app (weaken_expr e1) (weaken_expr e2);
  weaken_expr (new e)        := new (weaken_expr e);
  weaken_expr (deref l)      := deref (weaken_expr l);
  weaken_expr (assign l e)   := assign (weaken_expr l) (weaken_expr e).
Next Obligation.
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









(*
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

  unfold bind in H2.
  destruct (eval k arg env) eqn:Heq.
  specialize (H _ _ Heq).
  unfold usingEnv in H2. specialize (H0 v (all_cons v a) v').
  econstructor; eauto.
Admitted.
*)