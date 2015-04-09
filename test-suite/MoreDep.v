(* http://adam.chlipala.net/cpdt/html/MoreDep.html *)

Require Import Bool Arith List.
Require Import Program Equations.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Equations app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
  app _ Nil _ ls2 := ls2;
  app _ (Cons x ls1) _ ls2 := Cons x (app ls1 ls2).

  Equations inject (ls : list A) : ilist (length ls) :=
  inject nil := Nil;
  inject (cons h t) := Cons h (inject t).

  Equations unject n (ls : ilist n) : list A :=
  unject _ Nil := nil;
  unject _ (Cons x ls) := cons x (unject ls).

  Theorem unject_inverse : forall ls, unject (inject ls) = ls.
  Proof.
    intros. funelim (inject ls); simpl; simp unject.
    rewrite H. reflexivity.
  Qed.

  Equations hd n (ls : ilist (S n)) : A :=
  hd _ (Cons x _) := x.
End ilist.

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

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

Equations typeDenote (t : type) : Set :=
typeDenote Nat := nat;
typeDenote Bool := bool;
typeDenote (Prod t1 t2) := (typeDenote t1 * typeDenote t2)%type.
Set Printing Depth 10000.
Equations expDenote t (e : exp t) : typeDenote t :=
expDenote _ (NConst n) := n;
expDenote _ (Plus e1 e2) := expDenote e1 + expDenote e2;
expDenote _ (Eq e1 e2) <= eq_nat_dec (expDenote e1) (expDenote e2) => {
  | left _ := true;
  | right _ := false
}; (* := beq_nat (expDenote e1) (expDenote e2); *) 
expDenote _ (BConst b) := b;
expDenote _ (And e1 e2) := expDenote e1 && expDenote e2;
expDenote _ (If e e1 e2) <= expDenote e => {
  | true := expDenote e1;
  | false := expDenote e2
};
expDenote _ (Pair _ _ e1 e2) := (expDenote e1, expDenote e2);
expDenote _ (Fst _ _ e) := fst (expDenote e);
expDenote _ (Snd _ _ e) := snd (expDenote e).
Next Obligation.
  induction e; constructor; auto.
  destruct Nat.eq_dec; constructor; auto.
  destruct (expDenote e1); constructor; auto.
Defined.

Equations(nocomp) pairOutType2 (t : type) : Set :=
pairOutType2 (Prod t1 t2) := option (exp t1 * exp t2);
pairOutType2 _ := option unit.

Equations(nocomp) pairOutTypeDef (t : type) : Set :=
pairOutTypeDef (Prod t1 t2) := exp t1 * exp t2;
pairOutTypeDef _ := unit.

Transparent pairOutTypeDef. 
Definition pairOutType' (t : type) := option (match t with
                                               | Prod t1 t2 => exp t1 * exp t2
                                               | _ => unit
                                             end).

Equations pairOut t (e : exp t) : option (pairOutTypeDef t) :=
pairOut _ (Pair _ _ e1 e2) => Some (e1, e2);
pairOut _ _ => None.

(* Equations pairOut t (e : exp t) : pairOutType t := *)
(* pairOut _ (Pair _ _ e1 e2) => Some (e1, e2); *)
(* pairOut _ (If (Prod t1 t2) e e1 e2) =>  *)
(* pairOut _ _ => None. *)
 (* eq_nat_dec n1 n2 => { *)
 (*    | left _ := BConst true; *)
 (*    | right _ := BConst false *)
 (*  }; *)

Equations(struct e) cfold t (e : exp t) : exp t :=
cfold _ (NConst n) := NConst n;
cfold _ (Plus e1 e2) <= (cfold e1, cfold e2) => {
  | pair (NConst n1) (NConst n2) := NConst (n1 + n2);
  | pair e1' e2' := Plus e1' e2'
};
cfold _ (Eq e1 e2) <= (cfold e1, cfold e2) => {
  | pair (NConst n1) (NConst n2) := BConst (beq_nat n1 n2);
  | pair e1' e2' => Eq e1' e2'
};
cfold _ (BConst b) := BConst b;
cfold _ (And e1 e2) <= (cfold e1, cfold e2) => {
  | pair (BConst b1) (BConst b2) := BConst (b1 && b2);
  | pair e1' e2' := And e1' e2'
};
cfold _ (If _ e e1 e2) <= cfold e => {
  | BConst true := cfold e1;
  | BConst false := cfold e2;
  | e' := If e' e1 e2 (* FIXME wrong recursive call computed (cfold e1) (cfold e2) *)
};
cfold _ (Pair e1 e2) := Pair (cfold e1) (cfold e2);
cfold _ (Fst e) <= cfold e => {
  | e' <= pairOut e' => {
    | Some p := fst p;
    | None := Fst e'
  }
};
cfold _ (Snd e) <= cfold e => {
  | e' <= pairOut e' => {
    | Some p := snd p;
    | None := Snd e'
  }
}.

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Require Import Max Min Omega.

Section depth.
  Variable f : nat -> nat -> nat.

  Equations depth c n (t : rbtree c n) : nat :=
  depth _ _  Leaf := 0;
  depth _ _ (RedNode _ t1 _ t2) := S (f (depth t1) (depth t2));
  depth _ _ (BlackNode _ _ _ t1 _ t2) := S (f (depth t1) (depth t2)).
End depth.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
Proof.
  intros. funelim (depth Nat.min t); auto;
  match goal with
  | [ |- context[min ?X ?Y] ] =>
      let H := fresh in destruct (min_dec X Y) as [H|H]; rewrite H
  end; omega.
Qed.

Lemma depth_max' : forall c n (t : rbtree c n), match c with
                                                  | Red => depth max t <= 2 * n + 1
                                                  | Black => depth max t <= 2 * n
                                                end.
Proof.
  intros; funelim (depth Nat.max t); auto;
  match goal with
  | [ |- context[max ?X ?Y] ] =>
      let H := fresh in destruct (max_dec X Y) as [H|H]; rewrite H
  end;
  repeat match goal with
  | [ H : context[match ?C with Red => _ | Black => _ end] |- _ ] =>
      destruct C
  end; omega.
Qed.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
Proof.
  intros; generalize (depth_max' t); destruct c; omega.
Qed.

Theorem balanced : forall c n (t : rbtree c n), 2 * depth min t + 1 >= depth max t.
Proof.
  intros; generalize (depth_min t); generalize (depth_max t); omega.
Qed.

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Section present.
  Variable x : nat.

  Equations present c n (t : rbtree c n) : Prop :=
  present _ _ Leaf := False;
  present _ _ (RedNode _ a y b) := present a \/ x = y \/ present b;
  present _ _ (BlackNode _ _ _ a y b) := present a \/ x = y \/ present b.

  Equations rpresent n (t : rtree n) : Prop :=
  rpresent _ (RedNode' _ _ _ a y b) => present a \/ x = y \/ present b.
End present.

Notation "{< x >}" := (existT _ _ x).

(* No need for convoy pattern! *)
Equations balance1 n (a : rtree n) (data : nat) c2 (b : rbtree c2 n) : {c : color & rbtree c (S n)} :=
balance1 _ (RedNode' _ c0 _ t1 y t2) data _ d <= t1 => {
  | RedNode _ a x b := {<RedNode (BlackNode a x b) y (BlackNode t2 data d)>};
  | _ <= t2 => {
    | RedNode _ b x c := {<RedNode (BlackNode t1 y b) x (BlackNode c data d)>};
    | b := {<BlackNode (RedNode t1 y (* ? b *) t2) data d>}
  }
}.

Equations balance2 n (a : rtree n) (data : nat) c2 (b : rbtree c2 n) : {c : color & rbtree c (S n)} :=
balance2 _ (RedNode' _ c0 _ t1 z t2) data _ a <= t1 => {
  | RedNode _ b y c := {<RedNode (BlackNode a data b) y (BlackNode c z t2)>};
  | _ <= t2 => {
    | RedNode _ c z' d := {<RedNode (BlackNode a data t1) z (BlackNode c z' d)>};
    | _ := {<BlackNode a data (RedNode t1 z t2)>}
  }
}.

Section insert.
  Variable x : nat.

  Equations insResult (c : color) (n : nat) : Set :=
  insResult Red n := rtree n;
  insResult Black n := {c' : color & rbtree c' n}.

  Equations ins c n (t : rbtree c n) : insResult c n :=
  ins _ _ Leaf := {< RedNode Leaf x Leaf >};
  ins _ _ (RedNode _ a y b) <= le_lt_dec x y => {
    | left _ := RedNode' (projT2 (ins a)) y b;
    | right _ := RedNode' a y (projT2 (ins b))
  };
  ins _ _ (BlackNode c1 c2 _ a y b) <= le_lt_dec x y => {
    | left _ <= c1 => {
      | Red := balance1 (ins a) y b;
      | Black := {<BlackNode (projT2 (ins a)) y b>}
    };
    | right _ <= c2 => {
      | Red := balance2 (ins b) y a;
      | Black := {< BlackNode a y (projT2 (ins b))>}
    }
  }.

  Equations insertResult (c : color) (n : nat) : Set :=
  insertResult Red n := rbtree Black (S n);
  insertResult Black n := {c' : color & rbtree c' n}.

  Equations makeRbtree c n (r : insResult c n) : insertResult c n :=
  makeRbtree Red _ (RedNode' _ _ _ a x b) := BlackNode a x b;
  makeRbtree Black _ r := r.
  Next Obligation. destruct c; destruct r; simp makeRbtree. Defined.
  Arguments makeRbtree [c n] _.

  Equations insert c n (t : rbtree c n) : insertResult c n :=
  insert _ _ t := makeRbtree (ins t).

  Section present.
    Variable z : nat.

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance1 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof. intros. funelim (balance1 a y b); simpl in *; tauto. Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance2 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof. intros. funelim (balance2 a y b); simpl in *; tauto. Qed.

    Equations present_insResult (c : color) (n : nat) (t : rbtree c n) (r : insResult c n): Prop :=
    present_insResult Red n t r := rpresent z r <-> z = x \/ present z t;
    present_insResult Black n t r := present z (projT2 r) <-> z = x \/ present z t.

    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
    Proof.
      intros. funelim (ins t); simp present_insResult in *; simpl in *;
        try match goal with
          [ |- context [balance1 ?A ?B ?C] ] => generalize (present_balance1 A B C)
        end;
        try match goal with
          [ |- context [balance2 ?A ?B ?C] ] => generalize (present_balance2 A B C)
        end; tauto.
    Qed.

    Ltac present_insert t t0 :=
      intros; funelim (insert t); generalize (present_ins t0);
      try rewrite present_insResult_equation_1; try rewrite present_insResult_equation_2;
      funelim (ins t0); intro; assumption.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t)
      <-> (z = x \/ present z t).
    Proof. present_insert t t0. (* FIXME Qed. *) Admitted.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (projT2 (insert t))
      <-> (z = x \/ present z t).
    Proof. present_insert t t0. (* FIXME Qed. *) Admitted.
  End present.
End insert.
