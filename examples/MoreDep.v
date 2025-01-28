(** * MoreDep

  Porting a chapter of Adam Chlipala's Certified Programming with Dependent Types,
  #<a href="http://adam.chlipala.net/cpdt/html/MoreDep.html">More Dependent Types</a>#. *)

Require Import Bool Arith List Program. 
From Equations.Prop Require Import Equations.
Set Equations Transparent.

Set Keyed Unification.

Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).
  Derive Signature for ilist.
  Arguments Cons {n}.

  Equations app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
  app Nil ls2 := ls2;
  app (Cons x ls1) ls2 := Cons x (app ls1 ls2).

  Equations inject (ls : list A) : ilist (length ls) :=
  inject nil := Nil;
  inject (cons h t) := Cons h (inject t).

  Equations unject n (ls : ilist n) : list A :=
  unject Nil := nil;
  unject (Cons x ls) := cons x (unject ls).

  Theorem unject_inverse : forall ls, unject (inject ls) = ls.
  Proof.
    intros. funelim (inject ls); simp unject; congruence.
  Qed.

  Equations hd n (ls : ilist (S n)) : A :=
  hd (Cons x _) := x.
End ilist.

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.
Derive NoConfusion EqDec for type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool
| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t
| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

Derive Signature NoConfusion for exp.
Derive NoConfusionHom for exp.
Derive Subterm for exp.

Equations typeDenote (t : type) : Set :=
typeDenote Nat := nat;
typeDenote Bool := bool;
typeDenote (Prod t1 t2) := (typeDenote t1 * typeDenote t2)%type.

Equations expDenote t (e : exp t) : typeDenote t :=
expDenote (NConst n) := n;
expDenote (Plus e1 e2) := expDenote e1 + expDenote e2;
expDenote (Eq e1 e2) := Nat.eqb (expDenote e1) (expDenote e2);
expDenote (BConst b) := b;
expDenote (And e1 e2) := expDenote e1 && expDenote e2;
expDenote (If e e1 e2) with expDenote e => {
  | true := expDenote e1;
  | false := expDenote e2
};
expDenote (Pair e1 e2) := (expDenote e1, expDenote e2);
expDenote (Fst e) := fst (expDenote e);
expDenote (Snd e) := snd (expDenote e).

Equations pairOutType2 (t : type) : Set :=
pairOutType2 (Prod t1 t2) := option (exp t1 * exp t2);
pairOutType2 _ := option unit.

Equations pairOutTypeDef (t : type) : Set :=
pairOutTypeDef (Prod t1 t2) := exp t1 * exp t2;
pairOutTypeDef _ := unit.

Transparent pairOutTypeDef. 
Definition pairOutType' (t : type) := option (match t with
                                               | Prod t1 t2 => exp t1 * exp t2
                                               | _ => unit
                                             end).

Equations pairOut t (e : exp t) : option (pairOutTypeDef t) :=
pairOut (Pair e1 e2) => Some (e1, e2);
pairOut _ => None.

Set Printing Depth 1000000.

Require Import Wellfounded.

Equations cfold {t} (e : exp t) : exp t :=
(* Works with well-foundedness too: cfold e by wf (signature_pack e) exp_subterm := *)
cfold (NConst n) => NConst n;
cfold (Plus e1 e2) with (cfold e1, cfold e2) => {
  | pair (NConst n1) (NConst n2) := NConst (n1 + n2);
  | pair e1' e2' := Plus e1' e2'
};
cfold (Eq e1 e2) with (cfold e1, cfold e2) => {
  | pair (NConst n1) (NConst n2) := BConst (Nat.eqb n1 n2);
  | pair e1' e2' => Eq e1' e2'
};
cfold (BConst b) := BConst b;
cfold (And e1 e2) with (cfold e1, cfold e2) => {
  | pair (BConst b1) (BConst b2) := BConst (b1 && b2);
  | pair e1' e2' := And e1' e2'
};
cfold (If e e1 e2) with cfold e => {
  | BConst true => cfold e1;
  | BConst false => cfold e2;
  | _ => If e (cfold e1) (cfold e2) }
;
cfold (Pair e1 e2) := Pair (cfold e1) (cfold e2);
cfold (Fst e) with cfold e => {
  | e' with pairOut e' => {
    | Some p := fst p;
    | None := Fst e'
  }
};
cfold (Snd e) with cfold e => {
  | e' with pairOut e' => {
    | Some p := snd p;
    | None := Snd e'
  }
}.

Inductive color : Set := Red | Black.
Derive NoConfusion for color.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).
Derive Signature NoConfusion for rbtree.

Require Import Arith Lia.

Section depth.
  Variable f : nat -> nat -> nat.

  Equations depth {c n} (t : rbtree c n) : nat :=
  depth Leaf := 0;
  depth (RedNode t1 _ t2) := S (f (depth t1) (depth t2));
  depth (BlackNode t1 _ t2) := S (f (depth t1) (depth t2)).
End depth.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
Proof.
  intros. funelim (depth Nat.min t); cbn;
            auto;
  match goal with
  | [ |- context[min ?X ?Y] ] =>
      let H := fresh in destruct (Nat.min_dec X Y) as [H|H]; rewrite H
  end; lia.
Qed.

Lemma depth_max' : forall c n (t : rbtree c n), match c with
                                                  | Red => depth max t <= 2 * n + 1
                                                  | Black => depth max t <= 2 * n
                                                end.
Proof.
  intros; funelim (depth Nat.max t); cbn; auto;
  match goal with
  | [ |- context[max ?X ?Y] ] =>
      let H := fresh in destruct (Nat.max_dec X Y) as [H|H]; rewrite H
  end;
  repeat match goal with
  | [ H : context[match ?C with Red => _ | Black => _ end] |- _ ] =>
      destruct C
  end; lia.
Qed.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
Proof.
  intros; generalize (depth_max' t); destruct c; lia.
Qed.

Theorem balanced : forall c n (t : rbtree c n), 2 * depth min t + 1 >= depth max t.
Proof.
  intros; generalize (depth_min t); generalize (depth_max t); lia.
Qed.

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Section present.
  Variable x : nat.

  Equations present {c n} (t : rbtree c n) : Prop :=
  present Leaf := False;
  present (RedNode a y b) := present a \/ x = y \/ present b;
  present (BlackNode a y b) := present a \/ x = y \/ present b.

  Equations rpresent {n} (t : rtree n) : Prop :=
  rpresent (RedNode' a y b) => present a \/ x = y \/ present b.
End present.

Notation "{< x >}" := (sigmaI _ _ x).
Import Sigma_Notations.
(* No need for convoy pattern! *)
Equations balance1 n (a : rtree n) (data : nat) c2 (b : rbtree c2 n) : Σ c, rbtree c (S n) :=
balance1 (RedNode' t1 y t2) data d with t1 => {
  | RedNode a x b := {<RedNode (BlackNode a x b) y (BlackNode t2 data d)>};
  | _ with t2 => {
    | RedNode b x c := {<RedNode (BlackNode t1 y b) x (BlackNode c data d)>};
    | b := {<BlackNode (RedNode t1 y b) data d>}
  }
}.

Equations balance2 n (a : rtree n) (data : nat) c2 (b : rbtree c2 n) : Σ c, rbtree c (S n) :=
balance2 (RedNode' (c2:=c0) t1 z t2) data a with t1 => {
  | RedNode b y c := {<RedNode (BlackNode a data b) y (BlackNode c z t2)>};
  | _ with t2 => {
    | RedNode c z' d := {<RedNode (BlackNode a data t1) z (BlackNode c z' d)>};
    | _ := {<BlackNode a data (RedNode t1 z t2)>}
  }
}.

Section insert.
  Variable x : nat.

  Equations insResult (c : color) (n : nat) : Set :=
  insResult Red n := rtree n;
  insResult Black n := Σ c', rbtree c' n.
  Transparent insResult.
  
  Equations ins {c n} (t : rbtree c n) : insResult c n :=
  ins Leaf := {< RedNode Leaf x Leaf >};
  ins (RedNode a y b) with le_lt_dec x y => {
    | left _ := RedNode' (pr2 (ins a)) y b;
    | right _ := RedNode' a y (pr2 (ins b))
  };
  ins (@BlackNode c1 c2 _ a y b) with le_lt_dec x y => {
    | left _ with c1 => {
      | Red := balance1 (ins a) y b;
      | Black := {<BlackNode (pr2 (ins a)) y b>}
    };
    | right _ with c2 => {
      | Red := balance2 (ins b) y a;
      | Black := {< BlackNode a y (pr2 (ins b))>}
    }
  }.

  Equations insertResult (c : color) (n : nat) : Set :=
  insertResult Red n := rbtree Black (S n);
  insertResult Black n := Σ c', rbtree c' n.
  Transparent insertResult.
  
  Equations makeRbtree c n (r : insResult c n) : insertResult c n :=
  makeRbtree Red _ (RedNode' a x b) := BlackNode a x b;
  makeRbtree Black _ r := r.
  Arguments makeRbtree [c n] _.

  Equations insert {c n} (t : rbtree c n) : insertResult c n :=
  insert t := makeRbtree (ins t).

  Section present.
    Variable z : nat.

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (pr2 (balance1 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof. intros. funelim (balance1 a y b); subst; simpl in *; tauto. Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (pr2 (balance2 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof. intros. funelim (balance2 a y b); subst; simpl in *; tauto. Qed.

    Equations present_insResult (c : color) (n : nat) (t : rbtree c n) (r : insResult c n): Prop :=
    @present_insResult Red n t r := rpresent z r <-> z = x \/ present z t;
    @present_insResult Black n t r := present z (pr2 r) <-> z = x \/ present z t.

    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
    Proof.
      intros. funelim (ins t); simp present_insResult in *; simpl in *;
        try match goal with
          [ |- context [balance1 ?A ?B ?C] ] => generalize (present_balance1 A B C)
        end;
        try match goal with
          [ |- context [balance2 ?A ?B ?C] ] => generalize (present_balance2 A B C)
            end; try tauto.
    Qed.

    Ltac present_insert t t0 :=
      intros; funelim (insert t); cbn; generalize (present_ins t0);
      try rewrite present_insResult_equation_1; try rewrite present_insResult_equation_2;
      funelim (ins t0); intro; assumption.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t)
      <-> (z = x \/ present z t).
    Proof.
      intros.
      funelim (insert t).
      generalize (present_ins t). simpl.
      try rewrite present_insResult_equation_1; try rewrite present_insResult_equation_2.
      funelim (ins t). intros; assumption. intros; assumption.
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (pr2 (insert t))
      <-> (z = x \/ present z t).
    Proof. present_insert t t. Qed.
  End present.
End insert.
