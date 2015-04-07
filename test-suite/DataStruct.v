(* http://adam.chlipala.net/cpdt/html/DataStruct.html *)

Require Import Arith List.
Require Import Program Equations.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Equations get n (ls : ilist n) (i : fin n) : A :=
  get _ (Cons x _) First := x;
  get _ (Cons _ t) (Next j) := get t j.

End ilist.

Arguments Nil [A].
Arguments First [n].

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Equations imap n (ls : ilist A n) : ilist B n :=
  imap _ Nil := Nil;
  imap _ (Cons x t) := Cons (f x) (imap t).

  Theorem get_imap : forall n (i : fin n) (ls : ilist A n),
    get (imap ls) i = f (get ls i).
  Proof.
    intros. funelim (imap ls).
      - depelim i.
      - (* simp get. *) depelim i0.
        + repeat rewrite get_equation_2. reflexivity.
        + repeat rewrite get_equation_3. apply H.
  Qed.
End ilist_map.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Equations hget ls (mls : hlist ls) (i : member ls) : B elm :=
  hget _ (HCons _ _ x _) (HFirst _) := x;
  hget _ (HCons _ _ _ t) (HNext _ _ j) := hget t j.
End hlist.

Arguments HNil [A B].
Arguments HCons [A B x ls] _ _.

Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls] _.

Definition someTypes : list Set := nat :: bool :: nil.

Example someValues : hlist (fun T : Set => T) someTypes :=
  HCons 5 (HCons true HNil).

Goal hget someValues HFirst = 5.
Proof. (* simp hget. *)
  unfold someValues, someTypes. rewrite hget_equation_2. reflexivity.
Qed.

Goal hget someValues (HNext HFirst) = true.
Proof. (* simp hget. *)
  unfold someValues, someTypes. rewrite hget_equation_3. rewrite hget_equation_2. reflexivity.
Qed.

Inductive type : Set :=
| Unit : type
| Arrow : type -> type -> type.

Inductive exp : list type -> type -> Set :=
| Const : forall ts, exp ts Unit
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).

Arguments Const [ts].

Equations typeDenote (t : type): Set :=
typeDenote Unit := unit;
typeDenote (Arrow t1 t2) := typeDenote t1 -> typeDenote t2.

Equations expDenote ts t (e : exp ts t) (mls : hlist typeDenote ts) : typeDenote t :=
expDenote _ _ (Const _) _ := tt;
expDenote _ _ (Var _ _ mem) s := hget s mem;
expDenote _ _ (App _ _ _ e1 e2) s <= (expDenote e1 s) => {
  | e := e (expDenote e2 s)
};
expDenote _ _ (Abs _ _ _ e) s := fun x => expDenote e (HCons x s).

Section filist.
  Variable A : Set.

  Equations filist (n : nat) : Set :=
  filist 0 := unit;
  filist (S n) := (A * filist n)%type.

  Equations ffin (n : nat) : Set :=
  ffin 0 := Empty_set;
  ffin (S n) := option (ffin n).

  Equations fget {n} (ls : filist n) (i : ffin n) : A :=
(*  fget 0 _ i :=! i;*)
  fget (S n) (pair x _) None := x;
  fget (S n) (pair _ ls) (Some i) := fget ls i.
  Next Obligation. destruct i. Defined.
  Next Obligation. destruct i. Defined.
  Next Obligation. induction n; destruct i; destruct ls; simp fget. Defined.
End filist.

Arguments fget [A n] _ _.

Section filist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Equations fimap {n} (ls : filist A n) : filist B n :=
  fimap 0 tt := tt;
  fimap (S n) (pair x ls) := pair (f x) (fimap ls).

  Theorem fget_fimap : forall n (i : ffin n) (ls : filist A n),
    fget (fimap ls) i = f (fget ls i).
  Proof.
    intros. funelim (fimap ls); depelim i; simpl.
      - apply H.
      - reflexivity.
  Qed.
End filist_map.

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Equations fhlist (ls : list A) : Type :=
  fhlist nil := unit;
  fhlist (cons x ls) := (B x * fhlist ls)%type.

  Variable elm : A.

  Equations fmember (ls : list A) : Type :=
  fmember nil := Empty_set;
  fmember (cons x ls) := ((x = elm) + fmember ls)%type.

  Equations fhget (ls : list A) (mls : fhlist ls) (i : fmember ls) : B elm :=
  fhget nil _ i :=! i;
  fhget _ (pair x _) (inl eq_refl) := x;
  fhget (cons _ ls) (pair _ l) (inr i) := fhget ls l i.
  Next Obligation. destruct i. Defined.
  Next Obligation. destruct i. Defined.
  Next Obligation. induction ls; destruct i; subst; destruct mls; simp fhget. Defined.
End fhlist.
Arguments fhget [A B elm ls] _ _.

(*
Section tree.
  Variable A : Set.

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, ilist tree n -> tree.
End tree.

Section ifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Equations ifoldr n (ls : ilist A n) : B :=
  ifoldr _ Nil := i;
  ifoldr _ (Cons x ls) := f x (ifoldr ls).
End ifoldr.

Equations sum (t : tree nat) : nat :=
sum (Leaf n) := n;
sum (Node _ ls) := ifoldr (fun t n => sum t + n) 0 ls.

(* Fixpoint inc (t : tree nat) : tree nat :=
match t with
| Leaf n => Leaf (S n)
| Node _ ls => Node (imap inc ls)
end. *)

Equations(nocomp) inc (t : tree nat) : tree nat :=
inc (Leaf n) := Leaf (S n);
inc (Node _ ls) := Node (imap inc ls).

Goal inc (Leaf 0) = Leaf 1. Proof. simp inc. Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
Proof.
  intros. funelim (inc t); simp sum.
    - apply Le.le_n_Sn.
    - unfold inc_obligation_1.
Abort.
*)

Section tree.
  Variable A : Set.

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, (ffin n -> tree) -> tree.
End tree.
Arguments Node [A n] _.

Section rifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Equations rifoldr (n : nat) (get : ffin n -> A) : B :=
  rifoldr 0 _ := i;
  rifoldr (S n) get := f (get None) (rifoldr n (fun i => get (Some i))).
End rifoldr.
Arguments rifoldr [A B] _ _ [n] _.

Equations sum (t : tree nat) : nat :=
sum (Leaf n) := n;
sum (Node _ f) := rifoldr plus 0 (fun i => sum (f i)).

Equations inc (t : tree nat) : tree nat :=
inc (Leaf n) := Leaf (S n);
inc (Node _ f) := Node (fun i => inc (f i)).

Lemma sum_inc' : forall n (f1 f2 : ffin n -> nat),
  (forall i, f1 i >= f2 i) ->
  rifoldr plus 0 f1 >= rifoldr plus 0 f2.
Proof.
  intros.
  funelim (rifoldr plus 0 f1); simpl.
    - constructor.
    - apply Plus.plus_le_compat.
      + apply H0.
      + apply H. intros. apply H0.
Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
Proof.
  intros. induction t; simp inc sum. (* funelim (inc t); simp sum. *)
    - apply Le.le_n_Sn.
    - apply sum_inc'. assumption.
Qed.

Inductive type' : Type := Nat | Bool.

Inductive exp' : type' -> Type :=
| NConst : nat -> exp' Nat
| Plus : exp' Nat -> exp' Nat -> exp' Nat
| Eq : exp' Nat -> exp' Nat -> exp' Bool
| BConst : bool -> exp' Bool
| Cond : forall n t, (ffin n -> exp' Bool)
  -> (ffin n -> exp' t) -> exp' t -> exp' t.

Equations type'Denote (t : type') : Set :=
type'Denote Nat := nat;
type'Denote Bool := bool.

Section cond.
  Variable A : Set.
  Variable default : A.

  Equations cond (n : nat) (tests : ffin n -> bool) (bodies : ffin n -> A) : A :=
  cond 0 _ _ := default;
  cond (S n) tests bodies <= tests None => {
    | true := bodies None;
    | false := cond n (fun i => tests (Some i)) (fun i => bodies (Some i))
  }.
End cond.
Arguments cond [A] _ [n] _ _.

Equations exp'Denote t (e : exp' t) : type'Denote t :=
exp'Denote _ (NConst n) := n;
exp'Denote _  (Plus e1 e2) := (exp'Denote e1) + (exp'Denote e2);
exp'Denote _ (Eq e1 e2) (*<= eq_nat_dec*) := EqNat.beq_nat (exp'Denote e1) (exp'Denote e2) (*=> {
  | true := true;
  | false := false
}*);
exp'Denote _ (BConst b) := b;
exp'Denote _ (Cond _ _ tests bodies default) :=
  cond (exp'Denote default) (fun i => exp'Denote (tests i)) (fun i => exp'Denote (bodies i)).

Definition someExp' : exp' Nat := Cond 1 (fun _ => BConst true) (fun _ => Plus (NConst 1) (NConst 2)) (NConst 0).

Goal exp'Denote someExp' = 3.
Proof. simp exp'Denote. Qed.

Goal exp'Denote (Eq someExp' (NConst 3)) = true.
Proof. simp exp'Denote. Qed.

Section cfoldCond.
  Variable t : type'.
  Variable default : exp' t.
(*
  Equations cfoldCond (n : nat) (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t) : exp' t :=
  cfoldCond 0 _ _ := default;
  cfoldCond (S n) tests bodies <= tests None => {
    | BConst true := bodies None;
    | BConst false := cfoldCond n (fun i => tests (Some i)) (fun i => bodies (Some i));
    | _ <= cfoldCond n (fun i => tests (Some i)) (fun i => bodies (Some i)) => {
      | Cond n' _ tests' bodies' default' := default'; (*
          Cond (S n') (fun i => match i with
                                | None => tests None
                                | Some i => tests' i
                                end)
                      (fun i => match i with
                                | None => bodies None
                                | Some i => bodies' i
                                end)
               default';*)
     | e := Cond 1 (fun _ => tests None) (fun _ => bodies None) e
 }}.
*)
End cfoldCond.