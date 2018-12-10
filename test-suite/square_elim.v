From Equations Require Import Equations.
(** Taken from Agda issue 3034:
    https://github.com/agda/agda/issues/3034 *)

Inductive eqi {A : Type} : A -> A -> Type :=
| eqrefl {a} : eqi a a.

Derive NoConfusion for eqi.

Notation " x = y " := (eqi x y).
Notation " x = y " := (eqi x y) : type_scope.

Inductive Square {A : Type} : forall w x : A, w = x -> forall y, x = y -> forall z, y = z -> z = w -> Type :=
  square w : Square w w eqrefl w eqrefl w eqrefl eqrefl.

Derive NoConfusion for Square.

Set Equations Debug.

Lemma noc {A} {w x y z : A} {p q r s} (u v : Square w x p y q z r s) : Type.
Proof.
  depelim u.
  depelim v.
  exact True.
Defined.

Lemma noc_noconf {A} {w x y z : A} {p q r s} (u v : Square w x p y q z r s) (e : u = v) : noc u v.
Proof.
  destruct e.
  depelim a.
  exact I.
Defined.
Import Sigma_Notations.

Notation " p # e " := (@eq_rect _ _ _ e _ p) (at level 20).

Notation " p [ P ] # e " := (@eq_rect _ _ P e _ p) (at level 20).

Notation " p [ P ] ## e " := (@eq_rect_dep _ _ P e _ p) (at level 20).

Polymorphic Lemma eq_simplification_sigma1_dep_dep@{i j} {A : Type@{i}} {P : A -> Type@{i}}
  (x y : &{ x : A & P x }) {B : eq x y -> Type@{j}} :
  (forall e' : eq x.1 y.1, forall e : eq (@eq_rect A x.1 P x.2 y.1 e') y.2, B (pack_sigma_eq e' e)) ->
  (forall e : eq x y, B e).
Proof.
  intros. revert X.
  destruct e.
  intros X. simpl in *.
  apply (X eq_refl eq_refl).
Defined.

Polymorphic Definition distribute_sigma_eq@{i j} {A : Type@{i}} {B : A -> Type@{i}}
            {C : forall x : A, B x -> Type@{j}}
            {x y : A} {e : eq x y} {p : B x} {q : B y} {z : C x p} {w : C y q}
            (e1 : eq (e [fun x => B x] # p) q)
            (e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x e => C x (e [fun x => B x] # p)] ## z)) w)
             : eq (e [ fun x => @sigma@{j} _ (fun b : B x => C x b) ] # &(p & z)) &(q & w).
Proof. destruct e. simpl in *. destruct e1. simpl in *. destruct e2. apply eq_refl. Defined.

Set Universe Polymorphism.
(* Derive NoConfusion for sigma. *)
(* Next Obligation. destruct b. red. reflexivity. Defined. *)
(* Next Obligation. Defined. *)

Lemma simplify_eq_transport {A} {B : A -> Type} {C : forall x : A, B x -> Type}
      {x y : A} {e : eq x y} {z : &{ b : B x & C x b}} {w : &{ b : B y & C y b}}
        (P : @eq &{ x : B y & C y x } (e [ fun y => &{ b : B y & C y b } ] # z) w -> Type)
  : (forall e1 : (eq (e [fun x => B x] # z.1) w.1),
        forall e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x e => C x (e [fun x => B x] # z.1)] ## z.2)) w.2,
        P (distribute_sigma_eq e1 e2)) ->


    (forall e' : eq (e # z) w, P e').
Proof.
  intros.
  destruct e. simpl in *. destruct e'.
  specialize (X eq_refl eq_refl). simpl in X. exact X.
Defined.


Lemma simplify_eq_transport_inv {A} {B : A -> Type} {C : forall x : A, B x -> Type}
      {x y : A} {e : eq x y} {z : &{ b : B x & C x b}} {w : &{ b : B y & C y b}}
        (P : @eq &{ x : B y & C y x } (e [ fun y => &{ b : B y & C y b } ] # z) w -> Type)
  : (forall e' : eq (e # z) w, P e') ->
     (forall e1 : (eq (e [fun x => B x] # z.1) w.1),
        forall e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x e => C x (e [fun x => B x] # z.1)] ## z.2)) w.2,
        P (distribute_sigma_eq e1 e2)).
Proof.
  intros.
  destruct e. simpl in *. destruct z, w; simpl in *. destruct e1. simpl in *. destruct e2. apply X.
Defined.

Lemma eq_rect_constant {A B} (x y : A) (p q : B) (e : eq x y) :
  (e [ fun _ => B ] # p = q) -> p = q.
Proof. destruct e. simpl. trivial. Defined.

Lemma eq_rect_proj {A} {B : A -> Type} {C : forall x : A, B x -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B x & C x b }) :
  eq ((e [ fun x => &{ b : B x & C x b } ] # p).1) (e [ B ] # p.1).
Proof.
  destruct e. simpl. reflexivity.
Defined.

Lemma eq_rect_proj_dep {A} (x : A) {B : forall x' : A, eq x x' -> Type} {C : forall (x' : A) (e : eq x x'), B x' e -> Type} (y : A) (e : eq x y)
      (p : &{ b : B x eq_refl & C x eq_refl b }) :
  eq ((e [ fun x' (e : eq x x') => &{ b : B x' e & C x' e b } ] ## p).1) (e [ B ] ## p.1).
Proof.
  destruct e. simpl. reflexivity.
Defined.

Parameter prf : forall {A} (x : A) p, Square x x eqrefl x p x eqrefl eqrefl -> Type.
Definition J2 {A : Type} (x : A) (p : x = x) (s : Square x x eqrefl x p x eqrefl eqrefl) : prf x p s.
  generalize_eqs_sig s.
  destruct s.
  intros e.
  revert e.
  refine (eq_simplification_sigma1_dep _ _ _ _ _).
  simpl.
  refine (eq_simplification_sigma1_dep_dep _ _ _).
  simpl.
  intros e'. simpl.
  refine (simplify_eq_transport _ _). simpl.
  intros e1.
  refine (eq_simplification_sigma1_dep_dep _ _ _).
  intros e2.
  assert True.
  revert e2. rewrite eq_rect_proj.
  simpl.
  rewrite eq_rect_proj_dep.

  revert e1.
  simpl.
  epose (simplify_eq_transport_inv (e := e') (B := fun x => A) (C := fun x b => eqi x b) (z := &(x & _)) (w := &(w & _)) (fun _ => True)).
  simpl in t.
  refine (t _). clear t.
  intros e''. generalize (pack_sigma_eq e' e''). clear e' e''.
  cut (&(&(x & x) & @eqrefl _ x) = &(&(w & w) & @eqrefl _ w) :> &{ x : &{ x : A & A } & x.1 = x.2 }).
  simplify ?.
  simpl.



  simplify ?. simpl. simpl.
  revert e.

  revert e'.


  simpl.
  intros e2.
  generalize (pack_sigma_eq e1 e2).
  clear e1 e2.



  assert &(

  pose (distribute_sigma_eq e' e).
  destruct e'. simpl in *.

  intros e0.



  refine (simplify_eq_transport _ _). simpl.
  intros e1.


        (forall (e : x = w)
                (e'' : e # &(x & p & z) = &(y & q & w))
                (e''': e'' # &(x & p & z) = &(y & q & w))


  simpl. simpl in e'.
  intros e''0.
  refine (eq_simplification_sigma1_dep_dep _ _ _).
  simpl.
  intros e'''.



  simpl.

  revert e' e'' e'''.

  Lemma pack_eqs {A} (B : A -> Type) (C : forall x : A, B x -> Type)
        (x y : A) (p : B x) (q : B y) (z : C x p) (w : C y q) :
        (forall (e : x = w)
                (e'' : e # &(x & p & z) = &(y & q & w))
                (e''': e'' # &(x & p & z) = &(y & q & w))




  refine (eq_simplification_sigma1_dep_dep _ _ _ _ _).
  intros e''''. simpl.
  refine (eq_simplification_sigma1_dep_dep _ _ _ _ _).

  cut (&(&(w & w) & @eqrefl _ w) = &(&(w0 & w0) & @eqrefl _ w0) :> &{ x : &{ x : A & A } & x.1 = x.2 }).
  simpl.
  simpl.


  depelim s.


Lemma noconf_noc {A} {w x y z : A} {p q r s} (u v : Square w x y z p q r s) (f : noc u v) : u = v.
Proof.
  depelim u.
  revert f.
  generalize_eqs_sig v.
  destruct v.
  simpl.
  simpl.



  simplify ?.
  simpl.
  simplify ?.
  simpl.
  intros e.

  intros e'. rewrite <- e'.
  clear e'. depelim e.
  destruct e''2.
  destruct e''3.
  destruct e''4.

  rewrite <- H in f.
  exact I.
Defined.




Show Proof.  Equations noc {A} {w x y z : A} {p q r s} (u v : Square w x y z p q r s) : Type :=
  noc (square ?(w)) (square w) := _.

Parameter prf : forall {A} (x : A) p, Square x x x x eqrefl p eqrefl eqrefl -> Type.
Equations J2 {A : Type} (x : A) (p : x = x) (s : Square x x x x eqrefl p eqrefl eqrefl) : prf x p s :=
J2 _ _ (square x) := _.
