From Equations Require Import Equations.
Require Import Lia.
Set Transparent Equations.
Equations evenodd (b : bool) (n : nat) : Prop by rec n lt :=
  evenodd true 0 := True;
  evenodd true (S n) := evenodd false n;
  evenodd false 0 := False;
  evenodd false (S n) := evenodd true n.

Eval vm_compute in evenodd true 4.

Require Import List Wellfounded.
Set Asymmetric Patterns.

Polymorphic Inductive ty : forall (A : Type) (P : A -> Type), Type :=
| ty0 : ty nat (fun _ => nat)
| ty1 : ty (list nat) (fun _ => bool).

Polymorphic Derive Signature NoConfusion for ty.


Notation "{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99) : type_scope.
Notation "{ x & y }" := (@sigma _ (fun x : _ => y)%type) (x at level 99) : type_scope.

Notation "&( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
    (right associativity, at level 4,
     format "&( x ,  .. ,  y  ,  z )").

Polymorphic Equations rel : {A &{ P &{ _ : A & ty A P }}} -> {A & { P & {_ : A & ty A P}}} -> Prop :=
  rel &(A, P, a, ta) &(B, Q, b, tb) =>
  match ta in ty A P, tb in ty B Q return A -> B -> Prop with
  | ty0, ty0 => lt
  | ty1, ty1 => fun l l' => length l < length l'
  | ty0, ty1 => fun n l => n < length l
  | ty1, ty0 => fun l n => length l < n
  end a b.

Polymorphic Instance: WellFounded rel.
Proof. Admitted.
Require Import Arith.

Polymorphic Definition pack {A} {P} (x : A) (t : ty A P) :=
  (&(A, P, x, t)) : {A & {P & {_ : A & ty A P}}}.

Polymorphic Equations double_fn {A} {P} (t : ty A P) (x : A) : P x by rec (pack x t) rel :=
  double_fn ty0 n := n + 0;
  double_fn ty1 nil := true;
  double_fn ty1 (x :: xs) := 0 <? length xs + double_fn ty0 (length xs).
Next Obligation. Transparent rel. unfold rel. simp rel. cbn. auto with arith. Qed.

Definition fn0 := Eval compute in double_fn ty0.
Definition fn1 := double_fn ty1.

Lemma fn0_unfold n : fn0 n = n + 0.
Proof.
  unfold fn0; simp double_fn.
Qed.

Lemma fn1_unfold l : fn1 l = match l with nil => true | x :: xs => 0 <? length xs + fn0 (length xs) end.
Proof.
  unfold fn1; simp double_fn. destruct l. simp double_fn. simp double_fn. now rewrite fn0_unfold.
Qed.

Polymorphic Equations double_fn' {A} {P} (t : ty A P) (x : A) : P x by rec (pack x t) rel :=
  double_fn' ty0 n := n + 0;
  double_fn' ty1 l := aux l _
    where aux l' (H : length l' <= length l)  : _ by struct l' :=
    aux nil _ := true;
    aux (x :: xs) H := 0 <? length xs + double_fn' ty0 (length xs) + if aux xs _ then 0 else 1.
Obligation Tactic := idtac.
Next Obligation. intros. cbn. auto with arith. Defined.
Next Obligation. intros. cbn. auto with arith. Defined.
Next Obligation. auto with arith. Defined.

Definition fn0' := Eval compute in double_fn' ty0.
Definition fn1' := double_fn' ty1.

Lemma fn0'_unfold n : fn0' n = n + 0.
Proof.
  unfold fn0'; simp double_fn'.
Qed.

Lemma fn1'_unfold l : fn1' l = match l with nil => true | x :: xs => 0 <? length xs + fn0' (length xs) end.
Proof.
  unfold fn1'; simp double_fn'. destruct l. simp double_fn. simp double_fn'.
  destruct double_fn'_unfold_obligation_1. rewrite fn0'_unfold.  auto.
  rewrite fn0'_unfold.

Qed.
