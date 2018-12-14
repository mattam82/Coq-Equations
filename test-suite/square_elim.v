From Equations Require Import Equations.
(** Taken from Agda issue 3034:
    https://github.com/agda/agda/issues/3034 *)

Notation "( x , y , .. , z )" := (sigmaI _ .. (sigmaI _ x y) .. z) : core_scope.
Inductive Square {A : Type} : forall w x y z: A, w = x -> x = y -> y = z -> z = w -> Type :=
  square w : Square w w w w eq_refl eq_refl eq_refl eq_refl.

Derive NoConfusion for Square.

Set Universe Polymorphism.

Import Sigma_Notations.
Set Equations Transparent.

Obligation Tactic := idtac.
Lemma singleton_eq {A} (x : A) (p q : &{ y : A & x = y }) : p = q.
Proof.
  destruct p, q. destruct pr2. destruct pr3. reflexivity.
Defined.

Lemma pack_sigma {A} {B : A -> Type}
      (P : forall x : A, B x -> Type) :
      (forall (p : &{ x : A & B x }), P p.1 p.2) ->
      (forall (x : A) (y : B x), P x y).
Proof.
  intros. apply (X &(x & y)).
Defined.

Definition pr1_seq@{i} {A : Type@{i}} {P : A -> Type@{i}} {p q : sigma A P} (e : p = q) : p.1 = q.1.
Proof. destruct e. apply eq_refl. Defined.

Equations NoC_point_l {A} {x : A} (e e' : &{ y : _ & eq x y}) : Prop :=
  NoC_point_l (x, p) (y, q) := True.

Equations noc_point_l {A} {x : A} (e e' : &{ y : _ & eq x y}) (H : e = e') : NoC_point_l e e' :=
  noc_point_l (A:=A) (x:=x) (y, p) (z, q) H := I.

Equations noc_point_inv_l {A} {x : A} (e e' : &{ y : _ & eq x y}) (n : NoC_point_l e e') : e = e' :=
  noc_point_inv_l (A:=A) (x:=x) (y, p) (z, q) n := _.
Next Obligation.
  simpl. intros. red in n.
  revert z q n.
  refine (pack_sigma _ _).
  revert y p.
  refine (pack_sigma _ _).
  intros p p0. pose (singleton_eq _ p p0).
  destruct e. intros. reflexivity.
Defined.

Instance noc_point_noconf_l {A} {x : A} : NoConfusionPackage &{ y : _ & eq x y }.
Proof.
  unshelve econstructor.
  apply NoC_point_l.
  apply noc_point_l.
  apply noc_point_inv_l.
  intros [y e].
  destruct e. intros. destruct e. simpl. reflexivity.
Defined.


Equations NoC_point_r {A} {x : A} (e e' : &{ y : _ & eq y x}) : Prop :=
  NoC_point_r (sigmaI _ _ _) (sigmaI _ _ _) := True.

Equations noc_point_r {A} {x : A} (e e' : &{ y : _ & eq y x}) (H : e = e') : NoC_point_r e e' :=
  noc_point_r (sigmaI _ _ _) (sigmaI _ _ _) _ := I.

Equations noc_point_inv_r {A} {x : A} (e e' : &{ y : _ & eq y x}) (n : NoC_point_r e e') : e = e' :=
  noc_point_inv_r (sigmaI _ _ eq_refl) (sigmaI _ _ eq_refl) n := eq_refl.

Instance noc_point_noconf_r {A} {x : A} : NoConfusionPackage &{ y : _ & eq y x }.
Proof.
  unshelve econstructor.
  apply NoC_point_r.
  apply noc_point_r.
  apply noc_point_inv_r.
  intros [y e].
  destruct e. intros. destruct e. simpl. reflexivity.
Defined.

Equations NoC_hetero {A} (e e' : &{ p : &{ x : A & A } & eq p.1 p.2}) : Prop :=
  NoC_hetero (sigmaI _ (sigmaI _ x _) _) (sigmaI _ (sigmaI _ y _) _) := x = y.

Equations noc_hetero {A}  (e e' : &{ p : &{ x : A & A } & eq p.1 p.2 }) (H : e = e') : NoC_hetero e e' :=
  noc_hetero (sigmaI _ (sigmaI _ x _) _) (sigmaI _ (sigmaI _ _ _) _) eq_refl := eq_refl.

Lemma noc_hetero_inv {A}  (e e' : &{ p : &{ x : A & A } & eq p.1 p.2 }) (H : NoC_hetero e e') : e = e'.
Proof.
  destruct e as [[x y] e].
  destruct e' as [[x' y'] e''].
  simpl in *. destruct e, e''. red in H. destruct H. reflexivity.
Defined.

Instance noc_hetero_package {A} : NoConfusionPackage &{ p : &{ x : A & A } & eq p.1 p.2 }.
Proof.
  unshelve econstructor.
  apply NoC_hetero.
  apply noc_hetero.
  apply noc_hetero_inv.
  intros [[x y] e]. intros b <-. simpl in *. destruct e. simpl. reflexivity.
Defined.

(* Derive NoConfusionHom for eqi. *)

(* Next Obligation. *)


(* Notation " x = y " := (eqi x y). *)
(* Notation " x = y " := (eqi x y) : type_scope. *)


Set Equations Debug.

(* Lemma noc {A} {w x y z : A} {p q r s} (u v : Square w x y z p q r s) : Type. *)
(* Proof. *)
(*   depelim u. *)
(*   depelim v. *)
(*   exact True. *)
(* Defined. *)

(* Lemma noc_noconf {A} {w x y z : A} {p q r s} (u v : Square w x y z p q r s) (e : u = v) : noc u v. *)
(* Proof. *)
(*   destruct e. *)
(*   depelim u. *)
(*   exact I. *)
(* Defined. *)

Notation " p # e " := (@eq_rect _ _ _ e _ p) (at level 20).

Notation " p [ P ] # e " := (@eq_rect _ _ P e _ p) (at level 20).

Notation " p [ P ] ## e " := (@eq_rect_dep _ _ P e _ p) (at level 20, only parsing).

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

Monomorphic Inductive Iseq2 {A : Type} : forall x y: A, x = y -> y = x -> Type :=
  iseq2 w : Iseq2 w w eq_refl eq_refl.
Monomorphic Derive NoConfusion for Iseq2.


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

Polymorphic Definition distribute_sigma_eq_nondep@{i j} {A : Type@{i}} {B : Type@{i}}
            {C : forall x : A, B -> Type@{j}}
            {x y : A} {e : eq x y} {p : B} {q : B} {z : C x p} {w : C y q}
            (e1 : eq p q)
            (e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x e => C x p] ## z)) w)
             : eq (e [ fun x => @sigma@{j} _ (fun b : B => C x b) ] # &(p & z)) &(q & w).
Proof. destruct e. simpl in *. destruct e1. simpl in *. destruct e2. apply eq_refl. Defined.


Lemma simplify_eq_transport_nondep {A} {B : Type} {C : forall x : A, B -> Type}
      {x y : A} {e : eq x y} {z : &{ b : B & C x b}} {w : &{ b : B & C y b}}
        (P : @eq &{ x : B & C y x } (e [ fun y => &{ b : B & C y b } ] # z) w -> Type)
  : (forall e1 : (eq z.1 w.1),
        forall e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x => C x _] # z.2)) w.2,
        P (distribute_sigma_eq_nondep e1 e2)) ->


    (forall e' : eq (e # z) w, P e').
Proof.
  intros.
  destruct e. simpl in *. destruct e'.
  specialize (X eq_refl eq_refl). simpl in X. exact X.
Defined.


Polymorphic Definition distribute_sigma_eq_nondep'@{i j} {A : Type@{i}} {B : A -> Type@{i}}
            {C : A -> Type@{i}}
            {x y : A} {e : eq x y} {p : B x} {q : B y} {z : C x} {w : C y}
            (e1 : eq (e [B] # p) q)
            (e2 : eq (e [C] # z) w)
             : eq (e [ fun x => @sigma@{j} _ (fun _ : B x => C x) ] # &(p & z)) &(q & w).
Proof. destruct e. simpl in *. destruct e1. simpl in *. destruct e2. apply eq_refl. Defined.


Lemma simplify_eq_transport_nondep' {A} {B : A -> Type} {C : A -> Type}
      {x y : A} {e : eq x y} {z : &{ b : B x & C x}} {w : &{ b : B y & C y}}
        (P : @eq &{ _ : B y & C y } (e [ fun y => &{ b : B y & C y } ] # z) w -> Type)
  : (forall e1 : (eq (e # z.1) w.1),
        forall e2 : eq (e [fun x => C x] # z.2) w.2,
        P (distribute_sigma_eq_nondep' e1 e2)) ->
    (forall e' : eq (e # z) w, P e').
Proof.
  intros.
  destruct e. simpl in *. destruct e'.
  specialize (X eq_refl eq_refl). simpl in X. exact X.
Defined.

Polymorphic Definition distribute_sigma_eq_nondep_dep@{i j} {A : Type@{i}} {B : Type@{i}}
            {C : A -> B -> Type@{i}}
            {x y : A} {e : eq x y} {p : B} {q : B} {z : C x p} {w : C y q}
            (e1 : eq p q)
            (e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x => C x p] # z)) w)
             : @eq &{ x : _ & C y x } (e [ fun x => @sigma@{j} _ (fun b : B => C x b) ] # &(p & z)) (q, w).
Proof. destruct e. simpl in *. destruct e1. simpl in *. destruct e2. apply eq_refl. Defined.

Lemma simplify_eq_transport_nondep_dep {A} {B : Type} {C : A -> B -> Type}
      {x y : A} {e : eq x y} {z : &{ b : B & C x b}} {w : &{ b : B & C y b}}
        (P : @eq &{ b : B & C y b } (e [ fun y => &{ b : B & C y b } ] # z) w -> Type)
  : (forall (e1 : eq z.1 w.1)
            (e2 : eq (e1 [fun lhs => C y lhs] # (e [fun x => C x z.1] # z.2)) w.2),
            P (distribute_sigma_eq_nondep_dep e1 e2)) ->
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

Lemma simpl_eq_rect_constant {A B} (x y : A) (p : B) (e : eq x y) :
  (e [ fun _ => B ] # p) = p.
Proof. destruct e. simpl. trivial. Defined.

Lemma eq_rect_constant {A B} (x y : A) (p q : B) (e : eq x y) :
  ((e [ fun _ => B ] # p = q)) = (p = q).
Proof. destruct e. simpl. trivial. Defined.

Lemma eq_rect_dep_constant {A B} (x y : A) (p q : B) (e : eq x y) :
  ((e [ fun _ _ => B ] ## p = q)) = (p = q).
Proof. destruct e. simpl. trivial. Defined.

Lemma eq_rect_proj {A} {B : A -> Type} {C : forall x : A, B x -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B x & C x b }) :
  ((e [ fun x => &{ b : B x & C x b } ] # p).1) = (e [ B ] # p.1).
Proof.
  destruct e. simpl. reflexivity.
Defined.

Definition eq_trans2 {A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof. destruct p. exact q. Defined.

Lemma eq_rect_proj_nondep {A} {B : Type} {C : forall x : A, B -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B & C x b }) :
  ((e [ fun x => &{ b : B & C x b } ] # p).1) = p.1.
Proof.
  destruct e. simpl. reflexivity.
Defined.

Lemma simplify_eq_rect_proj_nondep {A} {B : Type} {C : forall x : A, B -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B & C x b }) q
      (P : (e [ fun x => &{ b : B & C x b } ] # p).1 = q -> Type) :
  (forall e' : p.1 = q, P (eq_trans2 (eq_rect_proj_nondep x y e p) e')) -> (forall x, P x).
Proof.
  destruct e. simpl. intros. apply (X x0).
Defined.

Lemma simplify_eq_rect_proj {A} {B : A -> Type} {C : forall x : A, B x -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B x & C x b }) q
      (P : (e [ fun x => &{ b : B x & C x b } ] # p).1 = q -> Type) :
  (forall e' : e [ B ] # p.1 = q, P (eq_trans2 (eq_rect_proj x y e p) e')) -> (forall x, P x).
Proof.
  destruct e. simpl. intros. apply (X x0).
Defined.

Lemma eq_rect_proj2 {A} {B : A -> Type} {C : forall x : A, B x -> Type} (x y : A) (e : eq x y)
      (p : &{ b : B x & C x b }) :
  eq ((e [ fun x => &{ b : B x & C x b } ] # p).2) (e [ fun x e => C x (e #p).1 ] ## p.2).
Proof.
  destruct e. simpl. reflexivity.
Defined.

Lemma eq_rect_proj_dep {A} (x : A) {B : forall x' : A, eq x x' -> Type} {C : forall (x' : A) (e : eq x x'), B x' e -> Type} (y : A) (e : eq x y)
      (p : &{ b : B x eq_refl & C x eq_refl b }) :
  eq ((e [ fun x' (e : eq x x') => &{ b : B x' e & C x' e b } ] ## p).1) (e [ B ] ## p.1).
Proof.
  destruct e. simpl. reflexivity.
Defined.

Notation " 'rew' H 'in' c " := (@eq_rect _ _ _ c _ H) (at level 20, only parsing).

Polymorphic
Definition pr2_seq@{i} {A : Type@{i}} {P : A -> Type@{i}} {p q : sigma A P} (e : p = q) :
  rew (pr1_seq e) in p.2 = q.2.
Proof. destruct e. apply eq_refl. Defined.

Lemma pack_sigma_eq_inv {A} {B : A -> Type} (x y : A) (p : B x) (q : B y)
      (P : forall e : x = y, e [B] # p = q -> Type) :
      (forall e : &(x & p) = &(y & q), P (pr1_seq e) (pr2_seq e)) ->
      (forall (e : x = y)
             (e' : e [B] # p = q), P e e').
Proof.
  intros. destruct e, e'. apply (X eq_refl).
Defined.

(* Lemma singleton_eq {A} {B : A -> Type} (x y : A) (e : x = y) (p : B x) (q : B y) *)
(*       (e' : &(x & p) = &(y & q)) : rew e in p = q. *)
(* Proof. *)
(*   destruct e. simpl. *)
(*   change q with &(y & q).2. *)
(*   revert e. change y with &(y & q).1 at 1 2 3. *)
(*   destruct e'. simpl. *)

Lemma refine_eq_left {A} {x y w : A} (e : y = x) (P : x = w -> Type) :
  (forall (H : y = w), P (e [fun x => x = w]# H)) ->
  (forall (H : x = w), P H).
Proof.
  destruct e. simpl. exact id.
Defined.

Section pathsigma.
  Universe i.
  Equations path_sigma {A : Type@{i}} {P : A -> Type@{i}} {u v : sigma A P}
            (p : u.1 = v.1) (q : rew p in u.2 = v.2)
    : u = v :=
    path_sigma (u:=(sigmaI _ _ _)) (v:=(sigmaI _ _ _)) eq_refl eq_refl := eq_refl.
End pathsigma.


Lemma pack_eq_sigma {A}
      (P : forall (x : A), x = x -> Type) :
      (forall (p : &{ x : A & x = x }), P p.1 p.2) ->
      (forall (x : A) (e : x = x), P x e).
Proof.
  intros. apply (X &(x & e)).
Defined.

Lemma eq_rect_trans
      {A} {x y z : A} {P : A -> Type} (e : x = y) (e' : y = z) (p : P x) :
  rew (eq_trans e e') in p = rew e' in (rew e in p).
Proof. destruct e'. simpl. reflexivity. Defined.

Lemma simplify_eq_rect_trans {A} {B : A -> Type} 
      {x y z : A} {e : eq x y} {e' : eq y z} {p : B x} {q : B z}
        (P : @eq (B z) (rew e' in (rew e in p)) q -> Type)
  : (forall e1 : (eq (rew (eq_trans e e') in p) q), P (eq_rect_trans e e' p [fun x => x = q] # e1)) ->
    (forall e'' : eq (rew e' in (rew e in p)) q, P e'').
Proof.
  intros.
  destruct e. simpl in *. destruct e'. apply (X e'').
Defined.

(* Lemma simplify_eqx A : forall (p q : &{ x : A & &{ y : A & eq x y }}), p = q ->  *)
(* Proof. *)
(*   intros [ x [y p]] [x' [y' q]]. destruct p. destruct q. reflexivity. *)

Lemma invIseq2 {A} (x : A) (e : x = x) (iseq : Iseq2 x x eq_refl e) : e = eq_refl.
  generalize_eqs_sig iseq.
  destruct iseq.

  simplify ?. simpl.
  refine (eq_simplification_sigma1_dep _ _ _ _ _).
  simpl.
  intros e0.
  refine (simplify_eq_transport _ _).
  simpl.
  revert e0.
  refine (pack_sigma_eq_inv _ _ _ _ _ _).
  pose (apply_noConfusion (A := &{ x' : _ & eq w x'})).
  refine (p _ _ _ _).
  simpl. unfold NoC_point_l.
  intros []. trivial.
Defined.

Lemma invIseq2' {A} (x : A) (e : x = x) (iseq : Iseq2 x x e eq_refl) : e = eq_refl.
  generalize_eqs_sig iseq.
  destruct iseq.

  simplify ?. simpl.
  refine (eq_simplification_sigma1_dep _ _ _ _ _).
  simpl.
  intros e0.
  refine (simplify_eq_transport_nondep' _ _).
  simpl.
  intros e' e''. revert e0 e'' e'.
  refine (pack_sigma_eq_inv _ _ _ _ _ _).
  pose (apply_noConfusion (A := &{ x' : _ & eq x' w})).
  refine (p _ _ _ _). simpl.
  unfold NoC_point_r.
  intros. exact e'.
Defined.

Lemma invIseq2d {A} (x : A) (e : x = x) (iseq : Iseq2 x x eq_refl e) :
  &{ H : eq_refl = e &
         (H [fun e => Iseq2 x x eq_refl e] # iseq2 x) = iseq }.
Proof.
  generalize_eqs_sig iseq.
  destruct iseq.

  simplify ?. simpl.
  refine (eq_simplification_sigma1_dep_dep _ _ _).
  simpl.
  intros e0.
  refine (simplify_eq_transport _ _).
  simpl.
  revert e0.
  refine (pack_sigma_eq_inv _ _ _ _ _ _).
  pose (apply_noConfusion (A := &{ x' : _ & eq w x'})).
  refine (p _ _ _ _).
  simpl. unfold NoC_point_l.
  intros [].
  intros ->.
  simpl. intros ->. exists eq_refl. simpl. exact eq_refl.
Defined.

Definition J {A} {x : A} (P : forall y : A, x = y -> Type)
           (p : P x eq_refl) (y : A) (e : x = y) : P y e.
  destruct e. exact p.
Defined.
Definition subst {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  eq_rect x P f y e.
Notation "p =_{ P ; e } q" := (subst (P:=P) e p = q) (at level 90, format "p  =_{ P ; e }  q").
Definition subst_expl {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  subst e f.
Notation " 'rewP' H 'at' P 'in' c " := (@subst_expl _ _ P _ H c) (at level 20).


Definition ap@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
  J@{i j} (fun y _ => f x = f y) (@eq_refl _ (f x)) y e.
(* aka ap *)

Lemma ap_iter {A B C} (f : A -> B) (g : B -> C) (x y : A) (e : x = y) :
  Top.ap g (Top.ap f e) = Top.ap (fun x => g (f x)) e.
Proof. revert y e. refine (Top.J _ _). reflexivity. Qed.

(* Lemma ap_subst2 {A B C} (f : C -> B) (x y : A) (e : x = y) (z w : A -> C) (p : z x = w x) : *)
(*   Top.ap f (subst2 (P:=fun x : A => z x = w x) p y e) = *)
(*   Top.subst2 (P := fun x : A => f (z x) = f (w x)) (Top.ap f p) y e. *)
(* Proof. revert y e. refine (Top.J _ _). simpl. reflexivity. Defined. *)

(* Definition apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) : *)
(*   subst p (f x) = f y := *)
(*   J (fun y p => subst p (f x) = f y) (@eq_refl _ (f x)) y p. *)
(* (* aka apd *) *)

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoin equivalence*)
Set Printing Universes.
Cumulative Class IsEquiv@{i} {A : Type@{i}} {B : Type@{i}} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

Record Equiv@{i} (A B : Type@{i}) := { equiv :> A -> B ; is_equiv :> IsEquiv equiv }.
Arguments equiv {A B} e.

Instance Equiv_IsEquiv {A B} (e : Equiv A B) : IsEquiv (equiv e).
Proof. apply is_equiv. Defined.

Definition inv_equiv {A B} (E: Equiv A B) : B -> A :=
  equiv_inv (IsEquiv:=is_equiv _ _ E).
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3).

Definition equiv_inv_equiv@{i} {A B : Type@{i}} {E: Equiv A B} (x : A) : inv_equiv _ (equiv E x) = x := eissect _ x.
Definition inv_equiv_equiv@{i} {A B : Type@{i}} {E: Equiv A B} (x : B) : equiv E (inv_equiv _ x) = x := eisretr _ x.
Definition equiv_adj@{i} {A B : Type@{i}} {E: Equiv A B} (x : A)
  : inv_equiv_equiv (equiv E x) = ap (equiv E) (equiv_inv_equiv x)
  := eisadj _ x.

Lemma ap_trans {A B} (f : A -> B) (x y z : A) (e : x = y) (e' : y = z) :
  ap f (eq_trans e e') = eq_trans (ap f e) (ap f e').
Proof.
  destruct e, e'. reflexivity.
Defined.

Lemma ap_sym {A B} (f : A -> B) (x y : A) (e : x = y) :
  ap f (eq_sym e) = eq_sym (ap f e).
Proof.
  destruct e. reflexivity.
Defined.

Equations concat {A} {x y z : A} (e : x = y) (e' : y = z) : x = z :=
concat eq_refl q := q.
Notation "p @ q" := (concat p q) (at level 60).

Equations concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @ p = p :=
concat_1p eq_refl := eq_refl.

Equations concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ eq_refl  = p :=
concat_p1 eq_refl := eq_refl.

Equations concat_Vp {A : Type} {x y : A} (p : x = y) :
  eq_sym p @ p = eq_refl :=
concat_Vp eq_refl := eq_refl.

Equations concat_pV {A : Type} {x y : A} (p : x = y) : p @ eq_sym p = eq_refl :=
concat_pV eq_refl := eq_refl.

Equations concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
concat_p_pp eq_refl _ _ := eq_refl.

Equations concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
    (r @ p x) @ ap g q = (r @ q) @ p y :=
concat_pp_A1 _ eq_refl eq_refl := concat_p1 _.

Equations whiskerL {A : Type} {x y z : A} (p : x = y)
           {q r : y = z} (h : q = r) : p @ q = p @ r :=
whiskerL _ eq_refl := eq_refl.

Equations whiskerR {A : Type} {x y z : A} {p q : x = y}
           (h : p = q) (r : y = z) : p @ r = q @ r :=
whiskerR eq_refl _ := eq_refl.

Equations moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_sym q @ p = eq_refl -> p = q :=
moveL_M1 _ eq_refl := fun e => e.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
: eq_sym p = eq_sym q := ap (@eq_sym _ _ _) h.

Equations ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q :=
ap02 f eq_refl := eq_refl.

Equations ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q) :=
ap_p_pp f _ eq_refl _ := concat_p_pp _ eq_refl _.

Equations ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p) :=
ap_compose f g eq_refl := eq_refl.

Equations concat_A1p {A : Type} {g : A -> A} (p : forall x, g x = x) {x y : A} (q : x = y) :
  (ap g q) @ (p y) = (p x) @ q :=
concat_A1p (g:=g) p (x:=x) eq_refl with p x, g x :=
  { concat_A1p p eq_refl eq_refl _ := eq_refl }.

Equations ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q) :=
ap_pp _ eq_refl eq_refl => eq_refl.

Equations concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ eq_sym q = p :=
concat_pp_V eq_refl eq_refl => eq_refl.

Equations ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (eq_sym p) = eq_sym (ap f p) :=
ap_V f eq_refl => eq_refl.

Hint Rewrite @ap_pp @ap_V : ap.
Hint Rewrite  @concat_pp_V : concat.

Equations concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) = q @ (p y) :=
concat_pA1 p eq_refl := concat_p1 (p _).

Equations concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (eq_sym p @ q) = q :=
concat_p_Vp eq_refl eq_refl := eq_refl.

Equations concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ eq_sym q) @ q = p :=
concat_pV_p eq_refl eq_refl := eq_refl.
Hint Rewrite @concat_pA1 @concat_p_Vp @concat_pV_p : concat.
Transparent concat.
Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  : (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  now rewrite !concat_p1.
  (* now simp concat. *)
Defined.

Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'
:= match h, h' with eq_refl, eq_refl => eq_refl end.

Reserved Notation "p @@ q" (at level 20).
Notation "p @@ q" := (concat2 p q)%equations : equations_scope.
Reserved Notation "p ^" (at level 3, format "p '^'").
Notation "p ^" := (eq_sym p%equations) : equations_scope.
Notation "f ^^-1" := (@equiv_inv _ _ f _) (at level 3).

Lemma ap_equiv_inv@{i} (Δ : Type@{i}) (T : Type@{i}) (f : Δ -> T) (x y : Δ) :
  IsEquiv f -> f x = f y -> x = y.
Proof.
  intros H.
  refine (fun q => (eissect f x)^  @  ap f^^-1 q  @  eissect f y).
Defined.

Axiom axiom_triangle : forall {A}, A.
Instance ap_is_equiv@{i +} (Δ : Type@{i}) (T : Type@{i}) (f : Δ -> T) (I : IsEquiv f) (u v : Δ) :
  IsEquiv (@ap _ _ f u v) :=
  { equiv_inv := _ }.
Proof.
  intros.
  - eapply ap_equiv_inv; eauto.
  - red.
    refine (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose (f^^-1) f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).
  - refine
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).
  - intros ->. apply axiom_triangle.
Defined.

Definition ap_equiv (Δ : Type) (T : Type) (f : Δ -> T) (E : IsEquiv f) (u v : Δ) : Equiv (u = v) (f u = f v) :=
  {| equiv := @ap _ _ f u v |}.

Polymorphic
Definition ind_pack_eq_inv {A : Type}
  {B : A -> Type} (x y : A) (p : B x) (q : B y)
  (e : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
  (i : @eq A x y)
  (ee : rewP e at fun z => eq z.1 y in i = eq_refl) :
  rew i in p = q.
Proof.
  revert i ee. change y with (@sigmaI A (fun x => B x) y q).1 at 1 3 4 7 8.
  unfold subst_expl.
  change q with (@sigmaI A (fun x => B x) y q).2 at 9.
  set (s :=@sigmaI A (fun x => B x) y q) in *. clearbody s. destruct e.
  simpl. intros i e. symmetry in e. destruct e. reflexivity.
Defined.
Polymorphic
Definition opaque_ind_pack_eq_inv {A : Type} {B : A -> Type} {x y : A}
  (i : @eq A x y) {p : B x} {q : B y} (G : p =_{B;i} q -> Type) (e : &(x & p) = &(y & q))
  (ee : rewP e at (fun z => eq z.1 y) in i = eq_refl)
  := G (@ind_pack_eq_inv A B x y p q e i ee).

Polymorphic
Lemma simplify_ind_pack {A : Type}
  (B : A -> Type) (x y : A) (p : B x) (q : B y) (i : x = y)
  (G : p =_{B;i} q -> Type) :
  (forall (exp : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
          (ee : rewP exp at (fun z => eq z.1 y) in i = eq_refl),
          G (@ind_pack_eq_inv A B x y p q exp i ee)) ->
  (forall e : p =_{B;i} q, G e).
Proof.
  intros H. intros e.
  specialize (H (pack_sigma_eq i e)). unfold opaque_ind_pack_eq_inv in H.
  destruct i, e. simpl in H. specialize (H eq_refl). simpl in G. apply H.
Defined.
Arguments simplify_ind_pack : simpl never.

Polymorphic
Lemma simplify_ind_pack' {A : Type}
  (B : A -> Type) (x y : A) (p : B x) (q : B y) (i : x = y)
  (G : i [B] # p = q -> Type) :
  (forall (exp : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
          (ee : eq_rect &(x & p) (fun z => eq z.1 y) i _ exp = eq_refl),
          G (@ind_pack_eq_inv A B x y p q exp i ee)) ->
  (forall e : i [B] # p = q, G e).
Proof.
  intros H. intros e.
  specialize (H (pack_sigma_eq i e)). unfold opaque_ind_pack_eq_inv in H.
  destruct i, e. simpl in H. specialize (H eq_refl). simpl in G. apply H.
Defined.
Arguments simplify_ind_pack : simpl never.

Polymorphic Definition pack_nondep_sigma_eq@{i}
            {A : Type@{i}} {P : Type@{i}} {x y : A} {p : P} {q : P}
  (e' : x = y) (e : p = q) : &(x & p) = &(y & q).
Proof. destruct e'. simpl in e. destruct e. apply eq_refl. Defined.

Set Printing Universes.
Polymorphic
Lemma eq_simplification_sigma1_nondep_dep@{i j} {A : Type@{i}} {B : Type@{i}}
  {x y : sigma@{i} _ (fun x : A => B)}
  {P : eq x y -> Type@{j}} :
  (forall e : x.1 = y.1, forall e' : x.2 = y.2, P (pack_nondep_sigma_eq@{i} e e')) ->
  (forall e : x = y, P e).
Proof.
  intros H. destruct e. apply (H eq_refl eq_refl).
Defined.

(* Lemma transport_pack_nondep_1 {A} (x : A) {B} (p q : B) (e1 : @eq_refl _ x = eq_refl) (e2 : p = q) (q : eq_refl = eq_refl) *)
(*         (t : x = _) : *)
(*     (pack_nondep_sigma_eq e1 e2) [fun x => x.1 = q] # t = e1 [fun x => x = q] # t. *)

Definition associate_sigma {A} {B : A -> Type} {C : forall x : A, B x -> Type}
      (x : &{ p : &{ x : A & B x } & C p.1 p.2 }) : &{ x : A & &{ b : B x & C x b }} :=
  &(x.1.1, x.1.2 & x.2).

Definition associate_sigma_inv {A} {B : A -> Type} {C : forall x : A, B x -> Type}
          (x : &{ x : A & &{ b : B x & C x b }}) : &{ p : &{ x : A & B x } & C p.1 p.2 } :=
    &(&(x.1 & x.2.1) & x.2.2).

Definition associate_sigma_inv_eq {A} {B : A -> Type} {C : forall x : A, B x -> Type}
           (x y : &{ x : A & &{ b : B x & C x b }})
           (e : x = y) : associate_sigma_inv x = associate_sigma_inv y.
Proof.
  destruct x as [a [b c]]. destruct e.
  unfold associate_sigma_inv. simpl. reflexivity.
Defined.

Definition associate_sigma_eq {A} {B : A -> Type} {C : forall x : A, B x -> Type}
           (P : forall (x y : &{ p : &{ x : A & B x } & C p.1 p.2 }) (e : x = y), Type) :

  (forall x y (e : x = y), P (associate_sigma_inv x) (associate_sigma_inv y) (associate_sigma_inv_eq x y e)) ->
  (forall x y (e : x = y), P x y e).
Proof.
  intros H. intros x ? <-. specialize (H (associate_sigma x) (associate_sigma x) eq_refl).
  apply H.
Defined.

Polymorphic Definition associate_sigma_eq' {A} {B : A -> Type} {C : forall x : A, B x -> Type}
           (x y : &{ p : &{ x : A & B x } & C p.1 p.2 })
           (P : (x = y)-> Type) :
  (forall (e : associate_sigma x = associate_sigma y),
      P (associate_sigma_inv_eq _ _ e)) ->
  (forall (e : x = y), P e).
Proof.
  intros H. intros <-. specialize (H eq_refl).
  apply H.
Defined.
(* Lemma rew_in_sigma_nondep {A} {C : A -> A -> B -> Type} *)
(*         (x y : A) (e : x = y) *)
(*         (x' y' : A) (e' : x' = y') *)
(*         (p : &{ b : B & C x x' b }) *)
(*         (q : &{ b : B & C y y' b }) : *)
(*     (e [ fun x => &{ b : B & C x y' b } ] # *)
(*        (e' [fun lhs => &{ b : B & C x lhs b }] # p) = q) -> *)
(*     &{ e' : p.1 = q.1 & e [ fun x => p.2 = q.2 }. *)

Polymorphic Definition pack_sigma_eq_indep@{i}
            {A : Type@{i}} {P : Type@{i}} {p q : A} {x : P} {y : P}
  (e' : p = q) (e : x = y) : &(p & x) = &(q & y).
Proof. destruct e'. simpl in e. destruct e. apply eq_refl. Defined.

Notation "p ..1" := (pr1_seq p) (at level 3).
Notation "p ..2" := (pr2_seq p) (at level 3).

Lemma rew_in_sigma_nondep {A} {C : A -> A -> Type}
        (x y : A) (e : x = y)
        (x' y' : A) (e' : x' = y')
        (p : C x x')
        (q : C y y') :
    (e [ fun x => C x y' ] #
       (e' [fun lhs => C x lhs] # p) = q) ->
    (@eq_rect _ &(x & x') (fun x => C x.1 x.2) p _ (pack_sigma_eq_indep e e')) = q.
Proof.
  destruct e, e'. simpl. trivial.
Defined.

Lemma rew_in_sigma_nondep_inv {A} {B} {C : A -> B -> Type}
        (x y : A) (e : x = y)
        (x' y' : B) (e' : x' = y')
        (p : C x x')
        (q : C y y') :
  (@eq_rect _ &(x & x') (fun x => C x.1 x.2) p _ (pack_sigma_eq_indep e e')) = q ->
      (e [ fun x => C x y' ] #
       (e' [fun lhs => C x lhs] # p) = q).
Proof.
  destruct e, e'. simpl. trivial.
Defined.

Lemma simplify_eq_rect_nested {A B} {C : A -> B -> Type}
      {x y : A} {e : x = y}
      {x' y' : B} {e' : x' = y'}
        (p : C x x')
        (q : C y y')
        (P : forall (x : (e [ fun x => C x y' ] #
                            (e' [fun lhs => C x lhs] # p) = q)), Type) :
  (forall (e'' :(@eq_rect _ &(x & x') (fun x => C x.1 x.2) p _ (pack_sigma_eq_indep e e')) = q),
      P (@rew_in_sigma_nondep_inv _ _ _ x y e x' y' e' p q e'')) ->
        (forall e, P e).
Proof.
  intros.
  destruct e, e'. simpl in *.
  apply X.
Defined.

(* Lemma eq_rect_f {A} {A'} (B : A' -> Type) (x y : A) (e : x = y) *)
(*         (f : A -> A') (p : B (f x)) (q : B (f y)) : *)
(*   ((f x, p) = (f y, q) :> &{ x : A' & B x }) -> *)
(*   e [fun x : A => B (f x)] # p = q. *)
(* Proof. *)
(*   destruct e. intros. simpl. *)


Ltac lower :=
  match goal with
    [ |- forall (e : @eq ?A _ _), _ ] =>
    let T := fresh in
    evar (T : Type);
    match goal with
    | [ T : _ |- _ ] => evar (f : A -> T)
    end
  end.


  (* Lemma apply_equiv_dom {A B} (P : B -> Type) (e : Equiv A B) : *)
  (*   (forall x : A, P (equiv e x)) -> forall x : B, P x. *)
  (* Proof. *)
  (*   intros. *)
  (*   specialize (X (e ^-1 x)). *)
  (*   rewrite inv_equiv_equiv in X. exact X. *)
  (* Defined. *)

  Lemma apply_equiv_dom {A B} (P : A -> Type) (e : Equiv A B) :
    (forall x : B, P (inv_equiv e x)) -> forall x : A, P x.
  Proof.
    intros.
    specialize (X (e x)).
    rewrite equiv_inv_equiv in X. exact X.
  Defined.
  (* intros. move H0 before x0. *)
  (* move H1 before y. *)
  (* revert_until H0. *)
  (* uncurry_hyps hyps. pattern sigma hyps. clearbody hyps. clear. set_eos. *)
  (* intros. *)
  (* uncurry_hyps hyps'. clearbody hyps'. revert hyps'. clear. revert hyps. set_eos. *)
  (* intros. *)
  (* uncurry_hyps hyps''. clearbody hyps''. revert hyps''. clear. *)
  (* intros h. exact h. *)
  (* simpl in f. *)
  (* subst H. *)
  (* unshelve evar (Hf : IsEquiv f). *)
  (* { unshelve econstructor. *)
  (*   intros H. decompose_sigmas. simpl in *. *)
  (*   unshelve eexists. exists pr1, pr9, pr0, pr4, pr10, pr3, pr5. exact pr6. *)
  (*   simpl. exact pr7. simpl. red. *)
  (*   intros [h h']. decompose_sigmas. subst f. simpl. destruct pr2. destruct pr11, pr7. reflexivity. *)
  (*   simpl. *)
  (*   intros [h h']. simpl in *. *)
  (*   revert h h'. curry. intros. reflexivity. simpl. *)
  (*   curry. curry. intros. reflexivity. } *)
  (* simpl in *. *)
  (* hidebody Hf. *)
  (* pose (ap_equiv _ _ f Hf). *)
  (* refine (apply_equiv_dom _ (e _ _) _). *)
  (* intros x0. unfold f in x0. simpl in x0. *)
  (* unfold eq_rect_r in x0. simpl in x0. *)
  (* revert x0. *)
  (* simplify ?. simpl. *)
  (* simplify ?. simpl. *)

Parameter prf : forall {A} (x : A) p, Square x x x x eq_refl p eq_refl eq_refl -> Type.
Definition J2 {A : Type} (x : A) (p : x = x) (s : Square x x x x eq_refl p eq_refl eq_refl) (pr : prf x eq_refl (square x)) : prf x p s.
  revert pr.
  generalize_eqs_sig s.
  destruct s.
  refine (eq_simplification_sigma1_dep _ _ _ _ _).
  simpl.
  unshelve lower.
  shelve.
  { set_eos.
    curry.
    intros ????. intros -> H' -> ->. uncurry_hyps h. exact h. }
  subst H.
  unshelve evar (Hf : IsEquiv f).
  { unshelve econstructor.
    intros [x' [H _]].
    exists x', x', x', x'.
    exists eq_refl. exists H. exists eq_refl. exact eq_refl.
    red.
    subst f. simpl.
    intros [x' [H u]]. unfold eq_rect_r. simpl. destruct u. exact eq_refl.
    subst f. simpl.
    intros (w' & x' & y & z & -> & H & -> & ->); simpl; exact eq_refl.
    apply axiom_triangle. }
  hidebody Hf.

  pose (ap_equiv _ _ f Hf).
  refine (apply_equiv_dom _ (e _ _) _).
  intros x0. unfold f in x0. simpl in x0.
  unfold eq_rect_r in x0. simpl in x0.
  revert x0.

  refine (eq_simplification_sigma1_dep_dep _ _ _).
  intros e'. move e' before x. revert w e'. cbn -[f e].
  refine (solution_right_dep _ _).
  cbn -[f e].
  refine (eq_simplification_sigma1_dep_dep _ _ _).
  intros e'. simpl in e'. move e' before p. revert p e' s0. cbn -[f e].
  refine (solution_left_dep _ _).
  cbn -[f e].
  intros s0.
  pose (apply_noConfusion (A := unit)).
  refine (p _ _ _ _). clear p; cbn -[f e].
  intros []. intros H. compute in H.
  revert H. intros ->. clear f Hf e.

  trivial.
Defined.

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
