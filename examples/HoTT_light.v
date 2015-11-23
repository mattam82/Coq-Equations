Require Export Unicode.Utf8_core.
Require Import Coq.Program.Tactics Setoid.

Require Import Equations.Equations.

Set Standard Proposition Elimination Names.
Set Universe Polymorphism.
Set Primitive Projections.

Set Implicit Arguments.

Section TypeEq.
  Local Definition T := Type.

  Inductive equality (A : T) (a : A) : A -> T :=
  | eq_refl : equality a a.

  Equations(nocomp) eq_sym (A : T) (x y : A) (eq : equality x y) : equality y x :=
  eq_sym _ _ _ eq_refl := eq_refl _.

  Equations(nocomp) eq_trans (A : T) (x y z : A) (eq1 : equality x y) (eq2 : equality y z) : equality x z :=
  eq_trans _ _ _ _ eq_refl eq_refl := eq_refl _.
End TypeEq.

Arguments equality {A} _ _.
Arguments eq_refl {A} [a].

Require Import CRelationClasses CMorphisms.

Instance eq_reflexive A : Reflexive (@equality A).
Proof. exact (@eq_refl A). Defined.

Instance eq_symmetric A : Symmetric (@equality A).
Proof. exact (@eq_sym A). Defined.

Instance eq_transitive A : Transitive (@equality A).
Proof. exact (@eq_trans A). Defined.

Notation " x = y " := (@equality _ x y).
Notation " x = y " := (@equality _ x y) : type_scope.

Inductive prod (A B : Type) := pair : A -> B -> prod A B.

Notation " X * Y " := (prod X Y) : type_scope.
Notation " ( x , p ) " := (@pair _ _ x p).

Equations(nocomp) fst {A B} (p : A * B) : A :=
fst _ _ (pair a b) := a.
Transparent fst.

Equations(nocomp) snd {A B} (p : A * B) : B :=
snd _ _ (pair a b) := b.
Transparent snd.

Record sigma {A : Type} (P : A -> Type) := Build_sigma
  { proj1 : A ; proj2 : P proj1 }.

Notation " { x : T & P } " := (sigma (fun x : T => P)).

Notation " ( x ; p ) " := (@Build_sigma _ _ x p).

Notation "x .1" := (proj1 x) (at level 3).
Notation "x .2" := (proj2 x) (at level 3).


Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Equations ap {A B : T} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
ap _ _ _ _ _ eq_refl := eq_refl.
Transparent ap.

(** A typeclass that includes the data making [f] into an adjoin equivalence*)

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Notation "f ^^-1" := (@equiv_inv _ _ f _) (at level 3).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.


(* This definition has slightly changed: the match on the equality is external
   to the function. *)
Equations(nocomp) apD10 {A} {B : A -> Type} {f g : forall x, B x} (h : f = g) : f == g :=
apD10 A B f g eq_refl := fun h => eq_refl.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Axiom funext : Funext.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^^-1.

Equations transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
transport A P x y eq_refl u := u.
Transparent transport.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Equations path_sigma {A : Type} (P : A -> Type) (u v : sigma P)
  (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v :=
path_sigma _ _ (Build_sigma _ _) (Build_sigma _ _) eq_refl eq_refl := eq_refl.

Equations(nocomp) path_prod_uncurried {A B : Type} (z z' : A * B)
           (pq : (fst z = fst z') * (snd z = snd z')): z = z' :=
path_prod_uncurried _ _ (pair _ _) (pair _ _) (pair eq_refl eq_refl) := eq_refl.

Definition path_prod {A B : Type} (z z' : A * B) (e : fst z = fst z') (f : snd z = snd z') : z = z' :=
  path_prod_uncurried _ _ (e, f).

Equations path_prod_eq {A B : Type} (z z' : A * B) (e : fst z = fst z') (f : snd z = snd z') : z = z' :=
path_prod_eq _ _ (pair _ _) (pair _ _) eq_refl eq_refl := eq_refl.

Equations eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _ (ap fst p) (ap snd p) = p :=
eta_path_prod _ _ (pair _ _) _ eq_refl := eq_refl.

Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (pair x y) (pair x' y') p q.

Equations ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p :=
ap_fst_path_prod _ _ (pair _ _) (pair _ _) eq_refl eq_refl := eq_refl.

Equations ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q :=
ap_snd_path_prod _ _ (pair _ _) (pair _ _) eq_refl eq_refl := eq_refl.

Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z').
Proof.
  refine (BuildIsEquiv _ _ _).
  - exact (fun r => (ap fst r, ap snd r)).
  - intro ; apply eta_path_prod.
  - intros [p q]. exact (path_prod'
                          (ap_fst_path_prod p q)
                          (ap_snd_path_prod p q)). 
  - destruct z as [x y], z' as [x' y'].
    intros [p q]; simpl in p, q.
    destruct p, q; apply eq_refl.
Defined.

Class Contr (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Global Instance contr_forall A {P : A -> Type} {H : forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => @center _ (H a)).
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

Equations(nocomp) concat A (x y z : A) (e : x = y) (e' : y = z) : x = z :=
concat _ _ _ _ eq_refl q := q.
Infix "@@" := concat (at level 50).

Definition moveR_E A B (f:A -> B) {H : IsEquiv f} (x : A) (y : B) (p : x = f^^-1 y)
  : (f x = y)
  := ap f p @@ (@eisretr _ _ f _ y).

Lemma contr_equiv A B (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  eapply moveR_E.
  apply contr.
Qed.

Equations concat_1p {A : Type} {x y : A} (p : x = y) :
  eq_refl @@ p = p :=
concat_1p _ _ _ eq_refl := eq_refl.

Equations(nocomp) concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @@ eq_refl  = p :=
concat_p1 _ _ _ eq_refl := eq_refl.

Equations concat_Vp {A : Type} {x y : A} (p : x = y) :
  eq_sym p @@ p = eq_refl :=
concat_Vp _ _ _ eq_refl := eq_refl.

Equations concat_pV {A : Type} {x y : A} (p : x = y) : p @@ eq_sym p = eq_refl :=
concat_pV _ _ _ eq_refl := eq_refl.

Equations concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @@ (q @@ r) = (p @@ q) @@ r :=
concat_p_pp _ _ _ _ _ eq_refl _ _ := eq_refl.

Hint Rewrite @concat_p1 @concat_Vp @concat_pV : concat.

Instance equality_equiv A :
  Equivalence (@equality A) := {}.

Instance concat_morphism (A : Type) x y z :
  Proper (equality ==> equality ==> equality) (@concat A x y z).
Proof. reduce. destruct X. destruct X0. destruct x0. reflexivity. Defined.

Instance trans_co_eq_inv_arrow_morphism :
  ∀ (A : Type) (R : crelation A),
    Transitive R → Proper (R ==> respectful
                             equality (flip arrow)) R.
Proof. reduce. transitivity y. assumption. now destruct X1. Defined.

Equations concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
    (r @@ p x) @@ ap g q = (r @@ q) @@ p y :=
concat_pp_A1 _ _ _ _ _ eq_refl _ eq_refl := concat_p1 _.

Equations whiskerL {A : Type} {x y z : A} (p : x = y)
           {q r : y = z} (h : q = r) : p @@ q = p @@ r :=
whiskerL _ _ _ _ _ _ _ eq_refl := eq_refl.

Equations whiskerR {A : Type} {x y z : A} {p q : x = y}
           (h : p = q) (r : y = z) : p @@ r = q @@ r :=
whiskerR _ _ _ _ _ _ eq_refl _ := eq_refl.

Equations moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  eq_sym q @@ p = eq_refl -> p = q :=
moveL_M1 _ _ _ _ eq_refl := fun e => e.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
: eq_sym p = eq_sym q := ap (@eq_sym _ _ _) h.

Equations ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q :=
ap02 _ _ _ _ _ _ _ eq_refl := eq_refl.

Equations ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @@ (ap f (p @@ q)) = (r @@ ap f p) @@ (ap f q) :=
ap_p_pp _ _ _ _ _ _ _ _ eq_refl _ := concat_p_pp _ eq_refl _.

Equations ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun x => g (f x)) p = ap g (ap f p) :=
ap_compose _ _ _ _ _ _ _ eq_refl := eq_refl.

Equations(nocomp) concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @@ (p y) = (p x) @@ q :=
concat_A1p _ f p x y eq_refl with p x, f x :=
concat_A1p _ _ _ _ _ eq_refl eq_refl _ := eq_refl.

Notation " 'rew' H 'in' c " := (eq_rect_r _ c H) (at level 20).
Notation " 'rewd' H 'in' c " := (@eq_rect_dep_r _ _ _ c _ H) (at level 20).
Lemma concat_A1p_lemma {A} (f : A -> A) (p : forall x, f x = x) {x y : A} (q : x = y) :
  eq (concat_A1p p q) (concat_A1p p q).
Proof.
  funelim (concat_A1p p q).
  rewrite Heq0. simpl. rewrite <- Heq. simpl. reflexivity.
Qed.

Equations ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @@ q) = (ap f p) @@ (ap f q) :=
ap_pp _ _ _ _ _ _ eq_refl eq_refl => eq_refl.

Equations concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @@ q) @@ eq_sym q = p :=
concat_pp_V _ _ _ _ eq_refl eq_refl => eq_refl.

Equations ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (eq_sym p) = eq_sym (ap f p) :=
ap_V _ _ _ _ _ eq_refl => eq_refl.  

Hint Rewrite @ap_pp @ap_V : ap.
Hint Rewrite  @concat_pp_V : concat.

Equations concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @@ (ap f q) = q @@ (p y) :=
concat_pA1 _ _ p _ _ eq_refl := concat_p1 (p _).

Equations concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @@ (eq_sym p @@ q) = q :=
concat_p_Vp _ _ _ _ eq_refl eq_refl := eq_refl.

Equations concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @@ eq_sym q) @@ q = p :=
concat_pV_p _ _ _ _ eq_refl eq_refl := eq_refl.
Hint Rewrite @concat_pA1 @concat_p_Vp @concat_pV_p : concat.
Transparent concat.
Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
    (r @@ ap f q) @@ p y = (r @@ p x) @@ q.
  destruct q; simpl. now simp concat. (* FIXME rewrite @concat. *)
Defined.

Equations ap_p {A B : Type} (f : A -> B) {x y : A} (p q: x = y) (e : p = q) :
  ap f p = ap f q :=
ap_p _ _ _ _ _ p q eq_refl := eq_refl.

Instance ap_morphism (A : Type) (B : Type) x y f :
  Proper (@equality (@equality A x y) ==> @equality (@equality B (f x) (f y))) (@ap A B f x y).
Proof. reduce. now apply ap_p. Defined.

Instance reflexive_proper_proxy :
  ∀ (A : Type) (R : crelation A), Reflexive R → ∀ x : A, ProperProxy R x.
Proof. intros. reduce. apply X. Defined.

Instance isequiv_inverse A B (f:A -> B) (H:IsEquiv f) : IsEquiv (f^^-1) | 1000.
Proof.
  refine (BuildIsEquiv (@eissect _ _ f _) (@eisretr _ _ f _) _).
  intros b.
  rewrite <- (concat_1p (eissect _)).
  rewrite <- (concat_Vp  (ap f^^-1 (eisretr (f (f^^-1 b))))).
  rewrite (whiskerR (inverse2 (ap02 f^^-1 (eisadj (f^^-1 b)))) _).
  refine (whiskerL _ (eq_sym (concat_1p (eissect _))) @@ _).
  rewrite <- (concat_Vp (eissect (f^^-1 (f (f^^-1 b))))).
  rewrite <- (whiskerL _ (concat_1p (eissect (f^^-1 (f (f^^-1 b)))))).
  rewrite <- (concat_pV (ap f^^-1 (eisretr (f (f^^-1 b))))).
  apply moveL_M1.
  repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
  rewrite <- (concat_pp_A1 (fun a => eq_sym (eissect a)) _ _).
  rewrite (ap_compose f f^^-1).
  rewrite <- (ap_p_pp _ _ (ap f (ap f^^-1 (eisretr (f (f^^-1 b))))) _).
  rewrite <- (ap_compose f^^-1 f).
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite ap_pp, concat_p_pp.
  rewrite (concat_pp_V _ (ap f^^-1 (eisretr (f (f^^-1 b))))).
  repeat rewrite <- ap_V. rewrite <- ap_pp.
  rewrite <- (concat_pA1 (fun y => eq_sym (eissect y)) _).
  rewrite ap_compose, <- (ap_compose f^^-1 f).
  rewrite <- ap_p_pp.
  rewrite (concat_A1p (@eisretr _ _ f _) _).
  rewrite concat_p_Vp.
  rewrite <- ap_compose.
  rewrite (concat_pA1_p (@eissect _ _ f _) _).
  rewrite concat_pV_p; apply concat_Vp.
Defined.

Definition path_contr A {H:Contr A} (x y : A) : x = y
  := concat (eq_sym (@contr _ H x)) (@contr _ H y).

Definition transport_inv A {P : A -> Type} (x y :A) (e : x = y) (u:P x) v:
  u = eq_sym e # v -> e # u = v.
  destruct e. exact id. 
Defined. 

Definition contr_sigma A {P : A -> Type}
  {H : Contr A} `{H0 : forall a, Contr (P a)}
  : Contr (sigma P).
Proof.
  exists (center A; center (P (center A))).
  intros [a Ha]. refine (path_sigma _ _ _ _).
  simpl. apply H. simpl. apply transport_inv.
  apply (H0 center).
Defined.

Equations(nocomp) path_sigma_uncurried (A : Type) (P : A -> Type) (u v : sigma P)
  (pq : sigma (fun p => p # u.2 = v.2))
  : u = v :=
  path_sigma_uncurried _ _ (Build_sigma u1 u2) (Build_sigma v1 v2) (Build_sigma eq_refl eq_refl) := eq_refl.
Transparent path_sigma_uncurried.

Definition pr1_path A `{P : A -> Type} {u v : sigma P} (p : u = v)
: u.1 = v.1
  := ap (@proj1 _ _) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path A `{P : A -> Type} {u v : sigma P} (p : u = v)
: p..1 # u.2 = v.2.
  destruct p. apply eq_refl.
Defined.

Notation "p ..2" := (pr2_path p) (at level 3).

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigma P}
           (p : u = v) : path_sigma_uncurried _ _ (p..1; p..2) = p.
  destruct p. apply eq_refl.
Defined.

Definition eta_path_sigma A `{P : A -> Type} {u v : sigma P} (p : u = v)
: path_sigma _ _ (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Definition path_sigma_equiv {A : Type} (P : A -> Type) (u v : sigma P):
  IsEquiv (path_sigma_uncurried u v).
  refine (BuildIsEquiv _ _ _).
  - exact (fun r => (r..1; r..2)).
  - intro. apply eta_path_sigma_uncurried.
  - destruct u, v; intros [p q]; simpl in *.
    destruct p. simpl in *. destruct q.
    reflexivity.
  - destruct u, v; intros [p q]; simpl in *;
    destruct p. simpl in *. destruct q; simpl in *.
    apply eq_refl.
Defined.

Instance contr_unit : Contr unit | 0 := let x := {|
  center := tt;
  contr := fun t : unit => match t with tt => eq_refl end
|} in x.


Definition path2_contr A {H:Contr A} {x y : A} (p q : x = y) : p = q.
  assert (K : forall (r : x = y), r = path_contr x y).
  intro r; destruct r; symmetry; now apply concat_Vp.
  apply (transitivity (y:=path_contr x y)).
  - apply K.
  - symmetry; apply K.
Defined.

Instance contr_paths_contr A {H:Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := concat (eq_sym (contr x)) (contr y);
  contr := path2_contr (concat (eq_sym (contr x)) (contr y))
|} in c.

Program Instance contr_prod A B {CA : Contr A} {CB : Contr B} : Contr (prod A B).
Next Obligation. exact (@center _ CA, @center _ CB). Defined.
Next Obligation. apply path_prod; apply contr. Defined.
