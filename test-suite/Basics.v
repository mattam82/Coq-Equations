(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Program Bvector List Relations.
From Equations Require Import Equations Signature.
Require Import Utf8.

Inductive le : nat -> nat -> Set :=
| le_0 n : le 0 (S n)
| le_S n m : le n m -> le (S n) (S m).
Derive Signature for le.

Equations congS {x y : nat} (p : x = y) : S x = S y :=
congS eq_refl := eq_refl.
  
(* Equations antisym {x y : nat} (p : le x y) (q : le y x) : x = y := *)
(* antisym (le_S n m p) (le_S ?(m) ?(n) q) := congS (antisym p q). *)

Module TestF.

  Equations(nocomp noind) f (n : nat) : nat :=
  f 0 := 42 ;
  f (S m)  with f m :=
  {
    f (S m) IH := _
  }.

End TestF.

Instance eqsig {A} (x : A) : Signature (x = x) A :=
  { signature a := x = a ;
    signature_pack e := sigmaI _ x e }.

Set Equations WithK.
Require Import DepElimK.
Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
K x P p eq_refl := p.
Unset Equations WithK.

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym x _ eq_refl := eq_refl.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans x _ _ eq_refl eq_refl := eq_refl.

Notation " x |:| y " := (@Vector.cons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@Vector.cons _ x n y) (at level 20, right associativity) : vect_scope.
(* Notation " [[ x .. y ]] " := (Vector.cons x .. (Vector.cons y Vector.nil) ..) : vect_scope. *)
Notation "[]v" := Vector.nil (at level 0) : vect_scope.

Section FilterDef.
  Context {A} (p : A -> bool).

  Equations filter (l : list A) : list A :=
  filter List.nil := List.nil ;
  filter (List.cons a l) with p a => {
                         | true := a :: filter l ;
                         | false := filter l }.

End FilterDef.

(* Equations filter {A} (l : list A) (p : A -> bool) : list A := *)
(* filter A List.nil p := List.nil ; *)
(* filter A (List.cons a l) p <= p a => { *)
(*   | true := a :: filter l p ; *)
(*   | false := filter l p }. *)

Inductive incl {A} : relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : incl xs ys -> incl (x :: xs) (x :: ys)
| skip {x : A} {xs ys : list A} : incl xs ys -> incl (xs) (x :: ys).

Global Transparent filter.

Equations sublist {A} (p : A -> bool) (xs : list A) : incl (filter p xs) xs :=
sublist p nil := stop ;
sublist p (cons x xs) with p x := {
  | true := keep (sublist p xs) ;
  | false := skip (sublist p xs) }.

(* Print Assumptions sublist. *)

Ltac rec ::= Subterm.rec_wf_eqns.

(* Derive Subterm for nat.  *)
Derive Signature for vector.
Derive NoConfusion NoConfusionHom for vector.
Derive Subterm for vector.

Require Import Arith Wf_nat.

Instance wf_nat : WellFounded lt := lt_wf.

Hint Resolve lt_n_Sn : lt.

Ltac solve_rec ::= simpl in * ; cbv zeta ; intros ; 
  try typeclasses eauto with subterm_relation Below lt.

Equations testn (n : nat) : nat
  by rec n lt :=
testn 0 := 0 ;
testn (S n) with testn n => {
  | 0 := S 0 ;
  | (S n') := S n' }.

Require Import Vectors.Vector.

Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.

Local Open Scope vect_scope.

Equations  vapp' {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  vapp' []v w := w ;
  vapp' (Vector.cons a v) w := Vector.cons a (vapp' v w).

(* Section vapp_def. *)
(*   Context {A : Type}. *)
(*   Equations  vapp' {n m} (v : vector A n) (w : vector A m) : vector A (n + m) := *)
(*   vapp' []v w := w ; *)
(*   vapp' (Vector.cons a n v) w := Vector.cons a (vapp' v w). *)
(* End vapp_def. *)

(* Print Assumptions vapp'. *)

From Equations Require Import EqDec.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n).
Proof.
  intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec h h0); subst. 
  destruct (IHx y). subst.
  left; reflexivity.
  right. intro. noconf H0. contradiction.
  right. intro. noconf H0. contradiction.
Defined.

(* Print Assumptions well_founded_vector_direct_subterm. *)

(** A closed proof of well-foundedness relying on the decidability
   of [A]. *)

Definition vector_subterm A := t_subterm A.

Instance well_founded_vector_direct_subterm' :
  forall A : Type, EqDec A -> WellFounded (vector_subterm A) | 0.
Proof.   intros. 
  apply Transitive_Closure.wf_clos_trans.
  intro. simp_sigmas. induction a.
  constructor; intros.
  simp_sigmas. simpl in *. 
  depelim H.
  constructor; intros.
  simp_sigmas. depelim H. 
  assumption.
Defined.
Print Assumptions well_founded_vector_direct_subterm'.

Instance eqdep_prod A B `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. intros. intros x y. decide equality. Defined.

Hint Unfold vector_subterm : subterm_relation.
(* Typeclasses Opaque vector_subterm. *)
Import Vector.

(* Section unzip_dec_def. *)
(*   Context {A B} `{EqDec A} `{EqDec B}. *)

(*   Equations unzip_dec {n} (v : vector (A * B) n) : vector A n * vector B n := *)
(*   unzip_dec n v by rec v (@vector_subterm (A * B)) := *)
(*   unzip_dec ?(O) nil := ([]v, []v) ; *)
(*   unzip_dec ?(S n) (cons (pair x y) n v) with unzip_dec v := { *)
(*      | pair xs ys := (cons x xs, cons y ys) }. *)
(* End unzip_dec_def. *)
Section foo.
  Context {A B} `{EqDec A} `{EqDec B}.

  Equations unzip_dec {n} (v : vector (A * B) n) : vector A n * vector B n
   by rec (signature_pack v) (@vector_subterm (A * B)) :=
  unzip_dec []v := ([]v, []v) ;
  unzip_dec ((x, y) |:| v) with unzip_dec v := {
    | pair xs ys := (cons x xs, cons y ys) }.
End foo.

Typeclasses Transparent vector_subterm.

(** Due to the packing of all arguments, can only be done in sections right now so
 that A and B are treated as parameters (better computational behavior anyway) *)
(* Equations unzip {A B} {n} (v : vector (A * B) n) : vector A n * vector B n := *)
(* unzip v by rec (signature_pack v) (@vector_subterm (A * B)) := *)
(* unzip nil := (nil, nil) ; *)
(* unzip (cons (pair x y) n v) <= unzip v => { *)
(*   | (pair xs ys) := (cons x xs, cons y ys) }. *)

(* Print Assumptions unzip. *)
(* Print Assumptions unzip_dec. *)

(*
Ltac generalize_by_eqs v ::= generalize_eqs v.

Equations unzip_n {A B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip_n A B O Vnil := (Vnil, Vnil) ;
unzip_n A B (S n) (cons (pair x y) n v) with unzip_n v := {
  | pair xs ys := (cons x xs, cons y ys) }. *)
(* Definition nos_with_comp (n : nat) := nat. *)
(* Lemma nos_with (n : nat) : nos_with_comp n. *)
(*   rec_wf_eqns nos n. *)

Equations nos_with (n : nat) : nat by rec n :=
nos_with O := O ;
nos_with (S m) with nos_with m := {
  | O := S O ;
  | S n' := O }.

(* Hint Unfold noConfusion_nat : equations. *)

Obligation Tactic := program_simpl ; auto with arith.

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := in_left ;
equal (S n) (S m) with equal n m => {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := in_right } ;
equal x y := in_right.

Import List.
Equations app_with {A} (l l' : list A) : list A :=
app_with nil l := l ;
app_with (cons a v) l with app_with v l => {
  | vl := cons a vl }.

(* Print Assumptions app_with. *)
(* About app_with_elim. *)
(* Print app_with_ind. *)
(* Print app_with_ind_ind. *)

(* Scheme app_with_elim := Minimality for app_with_ind Sort Prop *)
(*   with app_with_help_elim := Minimality for app_with_ind_1 Sort Prop. *)

(* About app_with_elim. *)

Equations plus' (n m : nat) : nat :=
plus' O n := n ; 
plus' (S n) m := S (plus' n m).

(* Ltac generalize_by_eqs id ::= generalize_eqs id. *)
(* Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars id. *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); auto. Qed.

Equations head A (default : A) (l : list A) : A :=
head A default nil := default ;
head A default (cons a v) := a.

Equations tail {A} (l : list A) : list A :=
tail nil := nil ;
tail (cons a v) := v.

(* Eval compute in @tail. *)
(* Eval compute in (tail (cons 1 nil)). *)

Equations app' {A} (l l' : list A) : (list A) :=
app' nil l := l ;
app' (cons a v) l := cons a (app' v l).

Global Transparent app'.

Notation  " x +++ y " := (@app' _ x y%list)  (at level 60, right associativity).

Equations rev_acc {A} (l : list A) (acc : list A) : list A :=
rev_acc nil acc := acc;
rev_acc (cons a v) acc := rev_acc v (a :: acc).

Equations rev {A} (l : list A) : list A :=
rev nil := nil;
rev (cons a v) := rev v +++ (cons a nil).

Notation " [] " := List.nil.


Lemma app'_nil : forall {A} (l : list A), l +++ [] = l.
Proof.
  intros.
  funelim (app' l []); auto.
  now rewrite H.
Qed.

Lemma app'_assoc : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. revert l''.
  funelim (l +++ l'); intros; simp app'. 
  rewrite H. reflexivity.
Qed.

Lemma rev_rev_acc : forall {A} (l : list A), rev_acc l [] = rev l.
Proof. intros. replace (rev l) with (rev l +++ []) by apply app'_nil.
  generalize (@nil A). 
  funelim (rev l). reflexivity.
  intros l'. simp rev_acc. rewrite H. 
  rewrite app'_assoc. reflexivity.
Qed.
Hint Rewrite @rev_rev_acc : rev_acc.

Lemma app'_funind : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof.
  intros.
  funelim (l +++ l'); simp app'.
  rewrite H. reflexivity. 
Qed.

Hint Rewrite @app'_nil @app'_assoc : app'.

Lemma rev_app' : forall {A} (l l' : list A), rev (l +++ l') = rev l' +++ rev l.
Proof. intros. funelim (l +++ l'); simp rev app'.
  now (rewrite H, <- app'_assoc).
Qed.
Equations zip' {A} (f : A -> A -> A) (l l' : list A) : list A :=
zip' f nil nil := nil ;
zip' f (cons a v) (cons b w) := cons (f a b) (zip' f v w) ;
zip' f x y := nil.

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : list A :=
zip'' f nil nil def := nil ;
zip'' f (cons a v) (cons b w) def := cons (f a b) (zip'' f v w def) ;
zip'' f nil (cons b w) def := def ;
zip'' f (cons a v) nil def := def.

Import Vector.

Equations vector_append_one {A n} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one nil a := cons a nil;
vector_append_one (cons a' v) a := cons a' (vector_append_one v a).

Equations vrev {A n} (v : vector A n) : vector A n :=
vrev nil := nil;
vrev (cons a v) := vector_append_one (vrev v) a.

Definition cast_vector {A n m} (v : vector A n) (H : n = m) : vector A m.
intros; subst; assumption. Defined.

Equations vrev_acc {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vrev_acc nil w := w;
vrev_acc (cons a v) w := cast_vector (vrev_acc v (cons a w)) _.
(* About vapp'. *)

Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.
Derive NoConfusion for vect. 

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : ∀ (xs : vector X m)(ys : vector X n), Split (vapp' xs ys).

Arguments Split [ X ].

(* Eval compute in @app'. *)
(* About nil. About vector. *)

Equations split {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs
  by rec m :=
split (m:=O) xs := append nil xs ;
split (m:=(S m)) (n:=n) (cons x xs) with split xs => {
  | append xs' ys' := append (cons x xs') ys' }.

Lemma split_vapp' : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros.
  funelim (vapp' v w).
  destruct split. depelim xs; intuition.
  simp split in *. destruct split. simpl.
  intuition congruence.
Qed.

(* Eval compute in @zip''. *)

Require Import Bvector.

Equations  split_struct {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs :=
split_struct (m:=0) xs := append nil xs ;
split_struct (m:=(S m)) (cons x xs) with split_struct xs => {
  split_struct (m:=(S m)) (cons x xs) (append xs' ys') := append (cons x xs') ys' }.

Lemma split_struct_vapp : ∀ (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split_struct (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros. funelim (vapp' v w); simp split_struct in *. 
  destruct (split_struct (m:=0) w). depelim xs; intuition.
  destruct (split_struct (vapp' t0 w)); simpl.
  intuition congruence.
Qed.

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead (cons a v) := a.

Equations vmap' {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap' f nil := nil ;
vmap' f (cons a v) := cons (f a) (vmap' f v).

Hint Resolve lt_n_Sn : subterm_relation.

Set Shrink Obligations.
Equations vmap {A B} (f : A -> B) {n} (v : vector A n) : vector B n
  by rec n :=
vmap f nil := nil ;
vmap f (cons a v) := cons (f a) (vmap f v).

Transparent vmap.

Transparent vmap'.
(* Eval compute in (vmap' id (@Vnil nat)). *)
(* Eval compute in (vmap' id (@cons nat 2 _ Vnil)). *)

(* Eval compute in @vmap'. *)

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.

  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  Equations inv (t : T) (im : Imf t) : S :=
  inv ?(f s) (imf s) := s.

End Image.

Section Univ.

  Inductive univ : Set :=
  | ubool | unat | uarrow (from:univ) (to:univ).

  Equations  interp (u : univ) : Set :=
  interp ubool := bool; interp unat := nat;
  interp (uarrow from to) := interp from -> interp to.

  (* Eval compute in interp. *)

  Transparent interp.

  Definition interp' := Eval compute in @interp.

  Equations foo (u : univ) (el : interp' u) : interp' u :=
  foo ubool true := false ;
  foo ubool false := true ;
  foo unat t := t ;
  foo (uarrow from to) f := id ∘ f.

  Transparent foo.
  (* Eval lazy beta delta [ foo foo_obligation_1 foo_obligation_2 ] iota zeta in foo. *)

End Univ.

(* Eval compute in (foo ubool false). *)
(* Eval compute in (foo (uarrow ubool ubool) negb). *)
(* Eval compute in (foo (uarrow ubool ubool) id). *)

Inductive foobar : Set := bar | baz.

Equations bla (f : foobar) : bool :=
bla bar := true ;
bla baz := false.

(* Eval simpl in bla. *)

Lemma eq_trans_eq A x : @eq_trans A x x x eq_refl eq_refl = eq_refl.
Proof. reflexivity. Qed.

Equations vlast {A} {n} (v : vector A (S n)) : A :=
vlast (cons a (n:=O) Vnil) := a ;
vlast (cons a (n:=S n) v) := vlast v.

Next Obligation.
  depind v. destruct n; simp vlast.
Defined.
Transparent vlast.
Eval compute in (vlast (cons 2 (cons 5 (cons 4 nil)))).

Fixpoint vapp {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  match v with
    | nil => w
    | cons a v' => cons a (vapp v' w)
  end.


(* Eval compute in (split (vapp Vnil (cons 2 Vnil))). *)
(* Eval compute in (split (vapp (cons 3 Vnil) (cons 2 Vnil))). *)

(* Recursive Extraction split. *)
(* Transparent split. *)
(* Eval cbv beta iota zeta delta [ split split_obligation_1 split_obligation_2  ] in @split. *)

Equations mult (n m : nat) : nat :=
mult O m := 0 ; mult (S n) m := mult n m + m.

Transparent mult.

(* Equations mult' (n m acc : nat) : nat := *)
(* mult' O m acc := acc ; mult' (S n) m acc := mult' n m (n + acc). *)

Inductive Parity : nat -> Set :=
| even : forall n, Parity (mult 2 n)
| odd : forall n, Parity (S (mult 2 n)).

(* Eval compute in (fun n => mult 2 (S n)). *)
Definition cast {A B : Type} (a : A) (p : A = B) : B.
  intros. subst. exact a.
Defined.

Unset Shrink Obligations.
Equations parity (n : nat) : Parity n :=
parity O := even 0 ;
parity (S n) with parity n => {
  parity (S ?(mult 2 k))     (even k) := odd k ;
  parity (S ?(S (mult 2 k))) (odd k)  := cast (even (S k)) _ }.

Equations half (n : nat) : nat :=
half n with parity n => {
  half ?(S (mult 2 k)) (odd k) := k ;
  half ?(mult 2 k) (even k) := k }.

Equations vtail {A n} (v : vector A (S n)) : vector A n :=
vtail (cons a v') := v'.

(** Well-founded recursion: note that it's polymorphic recursion in a sense:
    the type of vectors change at each recursive call. It does not follow
    a canonical elimination principle in this nested case. *)

Equations diag {A n} (v : vector (vector A n) n) : vector A n
 by rec n lt :=
diag nil := nil ;
diag (cons (cons a v) v') := cons a (diag (vmap vtail v')).

(** The computational content is the right one here: only the vector is
    matched relevantly, not its indices, which could hence
    disappear. *)

Extraction diag.

(** It can be done structurally as well but we're matching on the index now. *)
Equations(struct n) diag_struct {A n} (v : vector (vector A n) n) : vector A n :=
diag_struct (n:=O) nil := nil ;
diag_struct (n:=(S _)) (cons (cons a v) v') := cons a (diag_struct (vmap vtail v')).
Next Obligation.
  induction n. depelim v; constructor. depelim v. depelim h. simp diag_struct.
Defined.

Definition mat A n m := vector (vector A m) n.

Equations vmake {A} (n : nat) (a : A) : vector A n :=
vmake O a := nil ;
vmake (S n) a := cons a (vmake n a).

Equations vfold_right {A : nat -> Type} {B} (f : ∀ n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n :=
vfold_right f e nil := e ;
vfold_right f e (cons a v) := f _ a (vfold_right f e v).

Equations vzip {A B C n} (f : A -> B -> C) (v : vector A n) (w : vector B n) : vector C n :=
vzip f nil _ := nil ;
vzip f (cons a v) (cons a' v') := cons (f a a') (vzip f v v').

Definition transpose {A m n} : mat A m n -> mat A n m :=
  vfold_right (A:=λ m, mat A n m)
  (λ m', vzip (λ a, cons a))
  (vmake n nil).

(* Lemma vfold_right_e {A : Type} {B} {n} (f : ∀ n', B' -> vector (vector A 0) n' -> vector (vector A 0) (S n')) *)
(*   (e : vector (vector A 0) n) v : vfold_right f (vmake n Vnil) v =  *)
(* Typeclasses eauto :=. *)

Require Import Equations.Fin.

Generalizable All Variables.

Opaque vmap. Opaque vtail. Opaque nth.

Lemma nth_vmap `(v : vector A n) `(fn : A -> B) (f : fin n) : nth (vmap fn v) f = fn (nth v f).
Proof. revert B fn. funelim (nth v f); intros; simp nth vmap. Qed.

Lemma nth_vtail `(v : vector A (S n)) (f : fin n) : nth (vtail v) f = nth v (fs f).
Proof. funelim (vtail v); intros; simp nth. Qed.

Hint Rewrite @nth_vmap @nth_vtail : nth.
  
Lemma diag_nth `(v : vector (vector A n) n) (f : fin n) : nth (diag v) f = nth (nth v f) f.
Proof. revert f. funelim (diag v); intros f.
  depelim f.

  depelim f; simp nth.
  rewrite H. simp nth.
Qed.

Equations assoc (x y z : nat) : x + y + z = x + (y + z) :=
assoc 0 y z := eq_refl;
assoc (S x) y z with assoc x y z, x + (y + z) => {
assoc (S x) y z eq_refl _ := eq_refl }.
