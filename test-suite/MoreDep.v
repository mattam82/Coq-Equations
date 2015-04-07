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
(*
Equations expDenote t (e : exp t) : typeDenote t :=
expDenote _ (NConst n) := n;
expDenote _ (Plus e1 e2) := expDenote e1 + expDenote e2;
expDenote _ (Eq e1 e2) <= eq_nat_dec (expDenote e1) (expDenote e2) => {
  | left _ := true;
  | right _ := false
};
expDenote _ (BConst b) := b;
expDenote _ (And e1 e2) := expDenote e1 && expDenote e2;
expDenote _ (If e e1 e2) <= expDenote e => {
  | true := expDenote e1;
  | false := expDenote e2
};
expDenote _ (Pair _ _ e1 e2) := (expDenote e1, expDenote e2);
expDenote _ (Fst _ _ e) := fst (expDenote e);
expDenote _ (Snd _ _ e) := snd (expDenote e).
*)