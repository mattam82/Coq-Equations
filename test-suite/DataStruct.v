(* http://adam.chlipala.net/cpdt/html/DataStruct.html *)

Require Import Arith List.
Require Import Program Equations.Equations DepElimDec.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).
  Arguments First {n}.

  Derive Signature for ilist fin.

  Equations get {n} (ls : ilist n) (i : fin n) : A :=
  get (Cons x _) First := x;
  get (Cons _ t) (Next j) := get t j.

End ilist.

Arguments Nil [A].
Arguments First [n].

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Equations imap {n} (ls : ilist A n) : ilist B n :=
  imap Nil := Nil;
  imap (Cons x t) := Cons (f x) (imap t).

  Theorem get_imap : forall n (i : fin n) (ls : ilist A n),
    get (imap ls) i = f (get ls i).
  Proof.
    intros. funelim (imap ls).
      - depelim i.
      - depelim i0.
        + repeat rewrite get_equation_2. reflexivity.
        + repeat rewrite get_equation_3. apply H.
  Qed.
End ilist_map.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  #[universes(template)]
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  #[universes(template)]
  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Derive Signature NoConfusion for member.

  Equations hget {ls} (mls : hlist ls) (i : member ls) : B elm :=
  hget (HCons x _) (HFirst _) := x;
  hget (HCons _ t) (HNext _ j) := hget t j.
End hlist.

Arguments HNil [A B].
Arguments HCons [A B x ls] _ _.

Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls] _.

Definition someTypes : list Set := nat :: bool :: nil.

Example someValues : hlist (fun T : Set => T) someTypes :=
  HCons 5 (HCons true HNil).

Goal hget someValues HFirst = 5.
Proof. reflexivity. Qed.

Goal hget someValues (HNext HFirst) = true.
Proof. simp hget. Qed.

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

Equations expDenote {ts t} (e : exp ts t) (mls : hlist typeDenote ts) : typeDenote t :=
expDenote Const _ := tt;
expDenote (Var mem) s := hget s mem;
expDenote (App e1 e2) s with expDenote e1 s => {
  | e' := e' (expDenote e2 s)
};
expDenote (Abs e) s := fun x => expDenote e (HCons x s).

Equations filist (A : Set) (n : nat) : Set :=
  filist A 0 := unit;
  filist A (S n) := (A * filist A n)%type.

Global Transparent filist.

Equations ffin (n : nat) : Set :=
  ffin 0 := Empty_set;
  ffin (S n) := option (ffin n).
Global Transparent ffin.
  
Equations fget {A n} (ls : filist A n) (i : ffin n) : A :=
  fget (n:=(S n)) (pair x _) None := x;
  fget (n:=(S n)) (pair _ ls) (Some i) := fget ls i.

Section filist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Equations fimap {n} (ls : filist A n) : filist B n :=
  fimap (n:=0) tt := tt;
  fimap (n:=(S n)) (pair x ls) := pair (f x) (fimap ls).

  Theorem fget_fimap : forall n (i : ffin n) (ls : filist A n),
    fget (fimap ls) i = f (fget ls i).
  Proof.
    intros. funelim (fimap ls); depelim i; simp fget.
  Qed.
End filist_map.

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Equations fhlist (ls : list A) : Type :=
  fhlist nil := unit;
  fhlist (cons x ls) := (B x * fhlist ls)%type.
  Transparent fhlist.

  Variable elm : A.

  Equations fmember (ls : list A) : Type :=
  fmember nil := Empty_set;
  fmember (cons x ls) := ((x = elm) + fmember ls)%type.
  Transparent fmember.

  Equations fhget (ls : list A) (mls : fhlist ls) (i : fmember ls) : B elm :=
  fhget nil _ i :=! i;
  fhget _ (pair x _) (inl eq_refl) := x;
  fhget (cons _ ls) (pair _ l) (inr i) := fhget ls l i.

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
sum (Node f) := rifoldr plus 0 (fun i => sum (f i)).

Equations inc (t : tree nat) : tree nat :=
inc (Leaf n) := Leaf (S n);
inc (Node f) := Node (fun i => inc (f i)).
Import Sigma_Notations.

Transparent rifoldr.

Lemma sum_inc' : forall n (f1 f2 : ffin n -> nat),
  (forall i, f1 i >= f2 i) ->
  rifoldr plus 0 f1 >= rifoldr plus 0 f2.
Proof.
  intros.
  funelim (rifoldr plus 0 f1).
  - constructor.
  - apply Plus.plus_le_compat.
    + apply H0.
    + apply H. intros. apply H0.
Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
Proof.
  intros t. funelim (inc t); simp sum. auto.
  apply sum_inc'. intros; auto.
Qed.

Inductive type' : Type := Nat | Bool.
Derive NoConfusion for type'.

Inductive exp' : type' -> Set :=
| NConst : nat -> exp' Nat
| Plus : exp' Nat -> exp' Nat -> exp' Nat
| Eq : exp' Nat -> exp' Nat -> exp' Bool
| BConst : bool -> exp' Bool
| Cond : forall n t, (ffin n -> exp' Bool)
  -> (ffin n -> exp' t) -> exp' t -> exp' t.
Derive Signature NoConfusion NoConfusionHom for exp'.

Equations type'Denote (t : type') : Set :=
type'Denote Nat := nat;
type'Denote Bool := bool.

Section cond.
  Variable A : Set.
  Variable default : A.

  Equations cond (n : nat) (tests : ffin n -> bool) (bodies : ffin n -> A) : A :=
  cond 0 _ _ := default;
  cond (S n) tests bodies with tests None => {
    | true := bodies None;
    | false := cond n (fun i => tests (Some i)) (fun i => bodies (Some i))
  }.
End cond.
Arguments cond [A] _ [n] _ _.

Equations exp'Denote t (e : exp' t) : type'Denote t :=
exp'Denote (NConst n) := n;
exp'Denote (Plus e1 e2) := (exp'Denote e1) + (exp'Denote e2);
exp'Denote (Eq e1 e2) (*<= eq_nat_dec*) := EqNat.beq_nat (exp'Denote e1) (exp'Denote e2) (*=> {
  | true := true;
  | false := false
}*);
exp'Denote (BConst b) := b;
exp'Denote (Cond _ tests bodies default) :=
  cond (exp'Denote default) (fun i => exp'Denote (tests i)) (fun i => exp'Denote (bodies i)).

Definition someExp' : exp' Nat := Cond 1 (fun _ => BConst true) (fun _ => Plus (NConst 1) (NConst 2)) (NConst 0).

Goal exp'Denote someExp' = 3.
Proof. simp exp'Denote. Qed.

Goal exp'Denote (Eq someExp' (NConst 3)) = true.
Proof. simp exp'Denote. Qed.

Section cfoldCond.
  (* A weakness? of Equations: we cannot refine section variables:
     here in the inner clause we would need to refine [t] to Nat or Bool. *)

  Variable t : type'.
  Variable default : exp' t.

  Fail Equations cfoldCond (n : nat) (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t) : exp' t :=
  cfoldCond 0 _ _ := default;
  cfoldCond (S n) tests bodies with tests None => {
    | BConst true := bodies None;
    | BConst false := cfoldCond n (fun i => tests (Some i)) (fun i => bodies (Some i));
    | Eq e1 e2 with cfoldCond n (fun i => tests (Some i)) (fun i => bodies (Some i)) => {
      | Cond n' tests' bodies' default' :=
        Cond (S n') (fun i => match i with
                              | None => tests None
                              | Some i => tests' i
                              end)
             (fun i => match i with
                       | None => bodies None
                       | Some i => bodies' i
                       end)
             default';
      | e := Cond 1 (fun _ => tests None) (fun _ => bodies None) e };
    | _ := default }.
End cfoldCond.

Equations cfoldCond (t : type') (default : exp' t) {n : nat} (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t) : exp' t :=
cfoldCond default (n:=0) _ _ := default;
cfoldCond default (n:=(S n)) tests bodies with tests None => {
    | BConst true := bodies None;
    | BConst false := cfoldCond default (fun i => tests (Some i)) (fun i => bodies (Some i));
    | _ with cfoldCond default (fun i => tests (Some i)) (fun i => bodies (Some i)) => {
      | Cond n' tests' bodies' default' :=
        Cond (S n') (fun i => match i with
                              | None => tests None
                              | Some i => tests' i
                              end)
             (fun i => match i with
                       | None => bodies None
                       | Some i => bodies' i
                       end)
             default';
      | e := Cond 1 (fun _ => tests None) (fun _ => bodies None) e }}.

Fixpoint cfold t (e : exp' t) : exp' t :=
  match e with
    | NConst n => NConst n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp' Nat with
        | NConst n1, NConst n2 => NConst (n1 + n2)
        | _, _ => Plus e1' e2'
      end
    | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' return exp' Bool with
        | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
        | _, _ => Eq e1' e2'
      end

    | BConst b => BConst b
    | Cond n tests bodies default =>
      cfoldCond (cfold default)
      (fun idx => cfold (tests idx))
      (fun idx => cfold (bodies idx))
  end.

Lemma cfoldCond_correct : forall t (default : exp' t)
  n (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t),
  exp'Denote (cfoldCond default tests bodies)
  = exp'Denote (Cond n tests bodies default).
Proof.
  unshelve refine_ho (cfoldCond_elim _ _ _ _ _ _ _ _ _ _ _ _ _ _); simpl; intros.
  all:simpl; simp exp'Denote cond; rewrite ?H, ?Heq, ?Heq0;
    try rewrite ?Heq in Hind;
    simp exp'Denote cond;
  repeat (match goal with
          | [ |- context[cond_clause_2 _ _ ?E _] ] => destruct E; simp cond
          end).
Qed.
