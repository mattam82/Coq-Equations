Require Import Equations. Require Import Init.
Set Universe Polymorphism.
Open Scope sigma_scope.

Definition coerce {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  eq_rect x P f y e.
Arguments coerce : simpl never.

Polymorphic
Definition hetero_eq
  {A : Type} {B : A -> Type} {x y : A} (e : x = y) (p : B x) (q : B y) :=
  coerce e p = q.

Notation "p =_{ P ; e } q" := (hetero_eq (B:=P) e p q) (at level 90, format "p  =_{ P ; e }  q").

Definition apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  coerce p (f x) = f y.
Proof. now destruct p. Defined.
Definition ap {A B} (f : A -> B) {x y : A} (p : x = y) : f x = f y.
Proof. now destruct p. Defined.

Definition pr_eq1 {A} {B : A -> Type} {x y} {p : B x} {q : B y} (e : &(x & p) = &(y & q)) : x = y :=
  ap pr1 e.

Definition pr_eq2 {A} {B : A -> Type} {x y} {p : B x} {q : B y} (e : &(x & p) = &(y & q)) :
  p =_{ (fun s => B s.1) ; e } q :=
  apd (A:=sigma A B) pr2 e.

Definition pr_eq2' {A} {B : A -> Type} {x y} {p : B x} {q : B y} (e : &(x & p) = &(y & q)) :
  p =_{ B ; pr_eq1 e } q. red.
  change y with (pr1 &(y & q)).
  change q with (pr2 &(y & q)) at 4 5.
  destruct e. constructor.
Defined.

(* Lemma make_hetero_eq {A : Type}  *)
(*       (B : A -> Type) (x y : A) (e : x = y) (p : B x) (q : B y) *)
(*       (G : p =_{B; e} q -> Type) : *)
(*       (forall e : &(x & p) = &(y & q), G (pr_eq2' e)) -> *)
(*       (forall e : p =_{B;e} q, G e). *)

Definition pathover_move {A} {B : A -> Type} {x y} {p : B x} {q : B y}
  {e e' : x = y} (f : e = e') : p =_{B;e} q -> p =_{B;e'} q.
Proof.
  destruct f. intros X; exact X.
Defined.

Polymorphic
Lemma simplify_ind_fresh {A : Type} 
  (B : A -> Type) (x y : A) (e : x = y) (p : B x) (q : B y)
  (G : p =_{B;e} q -> Type) :
  (forall (e' : x = y) (f : p =_{B;e'} q) (q : e' = e), G (pathover_move q f)) ->
  (forall f : p =_{B;e} q, G f).
Proof.
  intros H. intros f.
  apply (H e f eq_refl).
Defined.
Arguments simplify_ind_fresh : simpl never.

Require Import Vector.

Lemma solution_left_inv : forall {A} {B : A -> Type} (t : A), (forall x, x = t -> B x) -> B t.
Proof. intros A B t H. apply (H t eq_refl). Defined.

Definition solution_inv_over {A} {B : A -> Type} (t : A) (x y : B t)
    (H : forall (e : t = t), x =_{B;e} y) : x = y :> B t := H eq_refl.

Definition solution_inv_over_goal {A} {B : A -> Type} (t : A) (x y : B t) (G : x = y -> Type)
           (H : forall (e : t = t) (f : x =_{B;e} y) (g : e = eq_refl), G (pathover_move g f)) :
  forall e : x = y, G e.
Proof.
  intros.
  apply (H eq_refl e eq_refl).
Defined.

Definition solution_inv_over_goal_inv {A} {B : A -> Type} (t : A) (x y : B t) (G : x = y -> Type)
           (H : forall e : x = y, G e) :
  forall (e : t = t) (f : x =_{B;e} y) (g : e = eq_refl), G (pathover_move g f).
Proof.
  intros. apply H.
Defined.

Derive NoConfusion for t.

(* Equations(nocomp) noConfusion_vect {A} {n} (v : t A n) {m} (v' : t A m) : Prop := *)
(* noConfusion_vect nil nil := True ; *)
(* noConfusion_vect (cons a n v) (cons a' n v') := @eq (sigma A (fun _ => sigma nat (t A))) *)
(*                                                 &(a , _ & v) &(a' , _ & v'); *)
(* noConfusion_vect _ _ := False. *)
(* Transparent noConfusion_vect. *)
(* Instance noConfusionVect_pack A : NoConfusionPackage &{ n : nat & t A n }. *)
(* Proof. *)
(*   unshelve econstructor. *)
(*   intros [n v] [m w]. exact (noConfusion_vect v w). *)
(*   intros a b ->. destruct b as [n v]. destruct v; reflexivity. *)
(*   intros [n v] [m w]. destruct v, w; simpl; intros; trivial; try contradiction. *)
(*   set (foo := &(h0, n0 & w)) in *. *)
(*   change n0 with foo.2.1. change h0 with foo.1. change w with foo.2.2. *)
(*   destruct H. simpl. reflexivity. *)

(*   simpl. intros a b ->. destruct b as [n v]. *)
(*   destruct v. reflexivity. *)
(*   simpl. reflexivity. *)
(* Defined. *)

Lemma pack_pathover {A} {B : A -> Type} {x y : A} (p : B x) (q : B y) :
  &{ e : x = y & p =_{B;e} q} -> &(x & p) = &(y & q).
Proof.
  intros [e He]. destruct e. intros. repeat red in He. unfold coerce in He.
  simpl in He. destruct He. reflexivity.
Defined.

Lemma unpack_pathover {A} {B : A -> Type} {x y : A} (p : B x) (q : B y) :
  &(x & p) = &(y & q) -> &{ e : x = y & p =_{B;e} q}.
Proof. intros e.
       exists (pr_eq1 e). apply pr_eq2'.
Defined.


Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoin equivalence*)

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Class Equiv (A B : Type) := { equiv : A -> B ; is_equiv : IsEquiv equiv }.

Instance sigma_pathover_isequiv {A} {B : A -> Type} {x y : A} (p : B x) (q : B y) :
  IsEquiv (pack_pathover p q) :=
  { equiv_inv := unpack_pathover p q }.
Proof.
  - intros e.
    set (foo := sigmaI B y q) in *.
    change q with foo.2.
    change y with foo.1. destruct e. simpl. reflexivity.
  - intros [e e'].
    destruct e. destruct e'. reflexivity.
  - intros [e e']. destruct e. destruct e'. reflexivity.
Defined.    
Instance sigma_pathover_equiv {A} {B : A -> Type} x y (p : B x) (q : B y) : Equiv _ _ := { equiv := pack_pathover p q }.

Definition uncurry {A} {B : A -> Type} {C : forall x : A, B x -> Type}
  (f : forall s : &{ x : A & B x }, C s.1 s.2) :
  forall (x : A) (b : B x), C x b :=
  fun x b => f &(x & b).

Notation " X <~> Y " := (Equiv X Y) (at level 90).

Definition equiv_functor_forall_covariant
           {A B} {P : A -> Type} {Q : B -> Type}
           (f : A <~> B)
           (g : forall a, P a <~> Q (@equiv _ _ f a))
  : (forall a, P a) <~> (forall b, Q b).
Proof.
Admitted.

Definition equiv_id A : A <~> A.
Admitted.

Definition equiv_iv {A B} : A <~> B -> B <~> A.
Admitted.

Require Import NoConfusion.
Goal forall {A} n (x y : A) (v v' : t A n) P (e : cons x v = cons y v'), P e.
Proof.
  intros. revert e.
  apply solution_inv_over_goal.
  refine (@apply_noConfusion _ (NoConfusionPackage_nat) _ _ _ _).
  simpl NoConfusion.
  

  
  simplify_one_dep_elim.
  
  refine (uncurry _).
  enough (forall (s : &(S n & @cons _ x n v) = &(S n & cons y v')) (g : pr_eq1 s = eq_refl),
             P (pathover_move g (pr_eq2' s))). admit.
  simpl NoConfusion.
  simplify_dep_elim.
  simpl in *. unfold pathover_move. simpl.
  destruct e. simpl in *.
  