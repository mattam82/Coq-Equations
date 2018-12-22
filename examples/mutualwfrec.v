From Equations Require Import Equations.
Require Import Lia.
Set Equations Transparent.
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

Definition fn0 := double_fn ty0.
Definition fn1 := double_fn ty1.

Lemma fn0_unfold n : fn0 n = n + 0.
Proof.
  unfold fn0. simp double_fn.
Qed.

Lemma fn1_unfold l : fn1 l = match l with nil => true | x :: xs => 0 <? length xs + fn0 (length xs) end.
Proof.
  unfold fn1; simp double_fn. destruct l. simp double_fn. simp double_fn. now rewrite fn0_unfold.
Qed.

(* Polymorphic Equations double_fn' {A} {P} (t : ty A P) (x : A) : P x by rec (pack x t) rel := *)
(*   double_fn' ty0 n := n + 0; *)
(*   double_fn' ty1 l := aux l _ *)
(*     where aux l' (H : length l' <= length l)  : _ by struct l' := *)
(*     aux nil _ := true; *)
(*     aux (x :: xs) H := 0 <? length xs + double_fn' ty0 (length xs) + if aux xs _ then 0 else 1. *)
(* Obligation Tactic := idtac. *)
(* Next Obligation. intros. cbn. auto with arith. Defined. *)
(* Next Obligation. intros. cbn. auto with arith. Defined. *)
(* Next Obligation. auto with arith. Defined. *)

(* Definition fn0' := Eval compute in double_fn' ty0. *)
(* Definition fn1' := double_fn' ty1. *)

(* Lemma fn0'_unfold n : fn0' n = n + 0. *)
(* Proof. *)
(*   unfold fn0'; simp double_fn'. *)
(* Qed. *)

(* Lemma fn1'_unfold l : fn1' l = match l with nil => true | x :: xs => 0 <? length xs + fn0' (length xs) end. *)
(* Proof. *)
(*   unfold fn1'; simp double_fn'. destruct l. simp double_fn. simp double_fn'. *)
(*   destruct double_fn'_unfold_obligation_1. rewrite fn0'_unfold.  auto. *)
(*   rewrite fn0'_unfold. *)
(* Admitted. *)

Require Import Equations.Subterm.

Equations ack (m n : nat) : nat by rec (m, n) (lexprod _ _ lt lt) :=
  ack 0 0         := 1;
  ack 0 (S n)     := S (S n);
  ack (S m) 0     := ack m 1;
  ack (S m) (S n) := ack m (ack (S m) n).

Module Abc.

Inductive abc : Set :=
| abc0
  | A (a : abc)
  | B (b : abc)
  | C (c : abc).

(* Inductive sct0_rel : abc -> abc -> Prop := *)
(* | sct0_bc x : sct0_rel (B (C x)) (A x) *)
(* | sct0_a x : sct0_rel x (A x) *)
(* | sct0_b x : sct0_rel x (B x) *)
(* | sct0_c x : sct0_rel x (C x). *)
(* Hint Constructors sct0_rel : rec_decision. *)
(* Instance: WellFounded sct0_rel. *)
(* Admitted. *)

Fixpoint measure_abc (x : abc) :=
  match x with
  | abc0 => 0
  | A x => 3 + measure_abc x
  | B x => S (measure_abc x)
  | C x => S (measure_abc x)
  end.


Equations sct0 (x : abc) : nat by rec (measure_abc x) lt :=
  sct0 abc0 := 0;
  sct0 (A x) := sct0 (B (C x)) + sct0 x;
  sct0 (B x) := sct0 x;
  sct0 (C x) := sct0 x.
Solve Obligations with program_simpl; lia.

Fixpoint measure_abc' (x : abc) :=
  match x with
  | abc0 => 0
  | A x => S (measure_abc' x)
  | B x => S (measure_abc' x)
  | C x => S (measure_abc' x)
  end.

Equations f1g1 (x : abc) : unit by rec (measure_abc' x) lt :=
  f1g1 (A (A x)) := f1 x _
    where f1 x' (H : measure_abc' x' < measure_abc' (A x)) : _ := { f1 x _ := f1g1 (A x) };
  f1g1 _ := tt.
Next Obligation. auto with arith. Defined.

Equations f1g1' (x : abc) : unit by rec (measure_abc' x) lt :=
  f1g1' (A (A x)) := f1g1' (A x);
  f1g1' _ := tt.
End Abc.

Module sct2.

  Polymorphic Inductive ty : forall (A : Type) (P : A -> Type), Type :=
  | ty0 : ty (list nat * list nat)%type (fun _ => list nat)
  | ty1 : ty (list nat * list nat * list nat) (fun _ => list nat).

  Polymorphic Equations rel' : {A &{ P &{ _ : ty A P & A }}} -> {A & { P & {_ : ty A P & A}}} -> Prop :=
  rel' &(A', P, ta, a) &(_, Q, tb, b) =>
  match ta in ty A P, tb in ty B Q return A -> B -> Prop with
  | ty0, ty0 => fun '(l0, l1) '(l0', l1') => length l0 < length l0'
  | ty1, ty1 => fun '(l0, n, l1) '(l0', n', l1') => length l0 < length l0'
  | ty0, ty1 => fun '(l0, l1) '(l0', l1', l2') => length l0 < length l0'
  | ty1, ty0 => fun l n => True
  end a b.
  Transparent rel'.
  Polymorphic Instance: WellFounded rel'.
  Proof. Admitted.


  Polymorphic Definition pack {A} {P} (t : ty A P) (x : A) :=
  (&(A, P, t, x)) : {A & {P & {_ : ty A P & A}}}.

  Polymorphic Equations fg {A} {P} (t : ty A P) (x : A) : P x by rec (pack t x) rel' :=
    fg ty0 (nil, x) := x;
    fg ty0 (cons y ys, x) := 1 :: fg ty1 (ys, x, (cons y ys));
    fg ty1 (a, b, c) := 2 :: fg ty0 (a, app b c).

  (* TODO find order! *)
  Next Obligation. unfold rel'. cbn. exact I. Qed.
  Next Obligation. unfold rel'. cbn. Admitted.

End sct2.
