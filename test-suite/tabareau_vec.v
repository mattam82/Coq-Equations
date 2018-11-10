From Equations Require Import Equations DepElimDec HSets.
Set Universe Polymorphism.

Unset Equations WithK.

Inductive ℕ (E:Set) : Set :=
| O : ℕ E
| S : ℕ E -> ℕ E
| raise : E -> ℕ E.

Arguments O {_}.
Arguments S {_} _.

Inductive Vec E (A : Set) : ℕ E -> Set :=
  nil  : Vec E A O
| cons : forall {n} (x : A) (xs : Vec E A n), Vec E A (S n).

Arguments nil {_ _}.
Arguments cons {_ _ _} _ _.

Inductive vector_param E (A : Set) : forall (n : ℕ E), Vec E A n -> Set :=
  vnil_param : vector_param E A O nil
| vcons_param : forall (n : ℕ E) (a : A) (v : Vec E A n),
                  vector_param E A n v ->
                  vector_param E A (S n) (cons a v).
Derive Signature for vector_param.

Derive NoConfusion for ℕ.
Derive NoConfusion for Vec.
Derive NoConfusion for vector_param.

Import Sigma_Notations.
Open Scope equations_scope.

Polymorphic Definition sigma_eq_1 {A} {B : A -> Type} {x y : &{ x : A & B x }} :
  x = y -> x.1 = y.1.
 Proof.
  destruct 1. reflexivity.
 Defined.

Polymorphic Definition sigma_eq_2 {A} {B : A -> Type} {x y : &{ x : A & B x }} :
  forall e : x = y, (@eq_rect A x.1 B x.2 y.1 (f_equal pr1 e)) = y.2.
 Proof.
  destruct e. reflexivity.
Defined.

Polymorphic Definition make_sigma_eq {A} {B : A -> Type} {x y : A} {p : B x} {q : B y} :
  forall (e : x = y) (e' : @eq_rect A x B p y e = q), &(x & p) = &(y & q).
Proof.
  destruct e. simpl. destruct 1. reflexivity.
Defined.

Polymorphic Definition sigma_eq_1_make_sigma_eq {A} {B : A -> Type} {x y : A} {p : B x} {q : B y}
  (e : x = y) (e' : @eq_rect A x B p y e = q) : sigma_eq_1 (make_sigma_eq e e') = e.
Proof.
  destruct e. simpl. destruct e'. reflexivity.
Defined.

Definition sigma_eq_decomp {A} {B : A -> Type} (x y : sigma A B) :
  &{ e : x.1 = y.1 & @eq_rect A x.1 B x.2 y.1 e = y.2 } -> x = y.
Proof.
  intros [e e']. destruct x, y. simpl in *.
  destruct e. destruct e'. simpl. reflexivity.
Defined.

Lemma sigma_eq_1_sigma_eq_decomp (A : Type) (D : A -> Type) (x y : &{ x : A & D x}) e :
         sigma_eq_1 (sigma_eq_decomp x y e) = e.1.
Proof.
  destruct e as [e1 e2].
  destruct x, y; simpl in *. destruct e1. destruct e2.
  reflexivity.
Defined.

Polymorphic Definition sigma_eq_decomp_inv {A} {B : A -> Type} {x y : sigma A B} :
  x = y -> &{ e : x.1 = y.1 & @eq_rect A x.1 B x.2 y.1 e = y.2 }.
Proof. intros ->. exists eq_refl. simpl. exact eq_refl. Defined.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = f_equal f (eissect x)
}.
Arguments eisretr {A B}%type_scope {f%function_scope} {_} _.
Arguments eissect {A B}%type_scope {f%function_scope} {_} _.
Arguments eisadj {A B}%type_scope {f%function_scope} {_} _.
Arguments IsEquiv {A B}%type_scope f%function_scope.



(* Polymorphic *)
(*   Definition lemma1 {I : Type} {D : I -> Type} {A : Type} *)
(*   (v : A -> I) (t1 t2 : A) (ct1 : D (v t1)) (ct2 : D (v t2)) *)
(*   (e : @eq (sigma A (fun x => D (v x))) &(t1 & ct1) &(t2 & ct2)) : *)
(*   &{ e' : *)
(*        (@eq (sigma I (fun x => D x)) (sigmaI _ (v t1) (ct1)) &(v t2 & ct2)) *)
(*        & sigma_eq_1 e' = f_equal v (sigma_eq_1 e) }. *)
(* Proof. *)
(*   generalize (sigma_eq_2_cong (f:=v) (B:=fun a' => D a') e). *)
(*   simpl. *)
(*   generalize (@eq_refl _ (f_equal v (sigma_eq_1 e))). *)
(*   generalize (f_equal v (sigma_eq_1 e)) at 1. simpl. *)
(*   intros i ef. rewrite <- ef. intros ec. *)
(*   unshelve eexists. apply sigma_eq_decomp. simpl. exists i. apply ec. clear. *)
(*   rewrite sigma_eq_1_sigma_eq_decomp. simpl. reflexivity. *)
(* Defined. *)

(* Polymorphic *)
(* Definition lemma2 {I : Type} {D : I -> Type} {A : Type} {args : Type} *)
(*   (v : A -> I) (u : A -> I) (c : forall x : A, D (u x)) *)
(*   (t1 t2 : A) (ct1 : D (v t1)) (ct2 : D (v t2)) *)
(*   (injc : forall x y : A, *)
(*       @eq (sigma I (fun x => D x)) (sigmaI _ (u x) (c x)) &(u y & c y) -> *)
(*       @eq A x y) *)
(*   (injc_inv : forall x y : A, *)
(*       @eq A x y -> *)
(*       @eq (sigma I (fun x => D x)) (sigmaI _ (u x) (c x)) &(u y & c y)) *)
(*   (injc_inv_eq : *)
(*      forall (x y : A) *)
(*             (e : @eq (sigma I (fun x => D x)) (sigmaI _ (u x) (c x)) &(u y & c y)), *)
(*      sigma_eq_1 (injc_inv x y (injc x y e)) = f_equal u (injc x y e) *)
(*   ) *)
(*   (injc_sect : forall x y : A, *)
(*       forall e : &(u x & c x) = &(u y & c y), injc_inv x y (injc x y e) = e) *)
(*   (* (injcequiv : forall x y : A, IsEquiv (injc x y)) *) *)
(*   (e : @eq (sigma A (fun x => D (v x))) &(t1 & ct1) &(t2 & ct2)) *)
(*   (e' : &{ e' : *)
(*             (@eq (sigma I (fun x => D x)) (sigmaI _ (v t1) (ct1)) &(v t2 & ct2)) *)
(*             & sigma_eq_1 e' = f_equal v (sigma_eq_1 e) }) : *)
(*   &{ e'' : eq t1 t2 & f_equal v e'' = f_equal v (sigma_eq_1 e) }. *)
(* Proof. *)
(*   revert e'. *)
(*    revert e. *)
(* -  generalize (sigmaI (fun x => B x) y q). *)
(* -  intros s H. destruct H. reflexivity. *)
(*   specialize (injc_sect t1 t2). *)
(*   intros e. *)
(*   intros [ev Heq]. *)
(*   rewrite <- (injc_sect ev) in Heq. *)
(*   exists (injc t1 t2 ev). *)
(*   unshelve erewrite injc_inv_eq in Heq. *)
(*   exact Heq. *)
(*  Defined. *)

(* Polymorphic *)
(* Definition lemma1_lemma2 {I : Type} {D : I -> Type} {A : Type} *)
(*   (v : A -> I) *)
(*   (c : forall x : A, D (v x)) *)
(*   (injc : forall x y : A, *)
(*       @eq (sigma I (fun x => D x)) (sigmaI _ (v x) (c x)) &(v y & c y) -> *)
(*       @eq A x y) *)
(*   (injc_inv : forall x y : A, *)
(*       @eq A x y -> *)
(*       @eq (sigma I (fun x => D x)) (sigmaI _ (v x) (c x)) &(v y & c y)) *)
(*   (injc_sect : forall x y : A, *)
(*       forall e : &(v x & c x) = &(v y & c y), injc_inv x y (injc x y e) = e) *)
(*   (injc_inv_eq : *)
(*      forall (x y : A) *)
(*             (e : @eq (sigma I (fun x => D x)) (sigmaI _ (v x) (c x)) &(v y & c y)), *)
(*      sigma_eq_1(injc_inv x y (injc x y e)) = f_equal v (injc x y e)) *)
(*   (t1 t2 : A) *)
(*   (e : @eq (sigma A (fun x => D (v x))) &(t1 & c t1) &(t2 & c t2)) : *)
(*   &{ e' : eq t1 t2 & f_equal v e' = f_equal v (sigma_eq_1 e) }. *)
(* Proof. *)
(*   pose (lemma1 v c t1 t2 e). *)
(*   apply (lemma2 v c injc injc_inv); auto. *)
(* Defined. *)


(* Polymorphic *)
(*   Definition lemma {I : Type} {D : I -> Type} {A : Type} {A' : Type} (v : A' -> A) *)
(*   (cty : A -> I) *)
(*   (c : forall x : A, D (cty x)) *)
(*   (t1 t2 : A') (e : @eq (sigma A' (fun a' => D (cty (v a')))) &(t1 & c (v t1)) &(t2 & c (v t2))) : *)
(*   e = e. *)
(* Proof. *)
(*   generalize (sigma_eq_2_cong (f:=v) (B:=fun a' => D (cty a')) e). *)
(*   simpl. *)
(*   generalize (@eq_refl _ (f_equal v (sigma_eq_1 e))). *)
(*   generalize (f_equal v (sigma_eq_1 e)) at 1. simpl. *)
(*   intros i ef. rewrite <- ef. intros ec. *)
(*   revert i ec ef. *)
(*   generalize (v t2). *)
(*   revert ef. *)


(*   rewrite <- (sigma_eq_2 e). rewrite e'. reflexivity. *)
(* Defined. *)

(* Polymorphic *)
(* Definition ind_pack_eq_inv_refl  {A : Type} *)
(*            {B : A -> Type} {x : &{ x : A & B x}} (e' : eq_refl = sigma_eq_1 eq_refl) : *)
(*   ind_pack_eq_inv _ _ _ (@eq_refl _ x) e' = eq_refl. *)
(* Proof. *)
(*   unfold ind_pack_eq_inv. simpl. simpl in e'. *)
(*   destruct x. simpl. *)
(*   revert e'. simpl. *)
(*   reflexivity. *)
(* Defined. *)

(* Polymorphic *)
(* Definition ind_pack_eq_inv_equiv {A : Type} *)
(*   {B : A -> Type} {x : A} (p q : B x) (e : p = q) *)
(*   (e' : eq_refl = sigma_eq_1 (ind_pack_eq e)) : *)
(*   ind_pack_eq_inv _ _ _ (ind_pack_eq e) e' = e. *)
(* Proof. *)
(*   destruct e. simpl in *. unfold ind_pack_eq_inv. simpl. *)
(*   unfold eq_rect. *)
(*   revert e'. pattern (@eq_refl A x) at 2. *)
(* Defined. *)

Polymorphic
Definition sigma_eq_2_cong  {A A'} {B : A' -> Type} {f : A -> A'} {x y : &{ x : A & B (f x) }} :
  forall e : x = y,
    (@eq_rect A' (f x.1) (fun x : A' => B x) x.2 (f y.1) (f_equal f (sigma_eq_1 e))) = y.2.
Proof.
  destruct e. reflexivity.
Defined.
Polymorphic

Definition sigma_eq_2_cong' {A A'} {B : A' -> Type} {f : A -> A'} {x y : &{ x : A & B (f x) }} :
  forall e : x.1 = y.1,
    (@eq_rect A' (f x.1) (fun x : A' => B x) x.2 (f y.1) (f_equal f e)) =
    (@eq_rect A x.1 (fun x : A => B (f x)) x.2 y.1 e).
Proof.
  destruct e. reflexivity.
Defined.

(* Polymorphic *)
(* Definition sigma_eq_2_cong_gl  {A} {B : A -> Type} {f : A -> A} {x y : &{ x : A & B (f x) }} *)
(*   (G : &(f x.(pr1) & x.(pr2)) = &(f y.(pr1) & y.(pr2)) -> Type) : *)
(*   (forall (e : x.1 = y.1) *)
(*           (e' : @eq_rect A x.1 (fun x : A => B (f x)) x.2 y.1 e = y.2), *)
(*           G (d *)
(*   ), *)
(*   forall (e : x.1 = y.1) *)
(*          (e' : @eq_rect A (f x.1) (fun x : A => B x) x.2 (f y.1) (f_equal f e) = y.2), *)
(*     G (pack_sigma_eq (f_equal f e) e'). *)

(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

(* Polymorphic *)
(* Definition sigma_eq_2_cong_gl  {A} {B : A -> Type} {f : A -> A} {x y : &{ x : A & B x }} *)
(* (G : @eq (sigma A (fun x => B x)) x y -> Type) : *)
(*   (forall e :  *)
(*   forall e : x = y, G e. *)

(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)
(* Polymorphic *)
(*   Lemma sigma_eq_1_f_equal {A} {B : A -> Type} {A'} {B' : A' -> Type} *)
(*         (x y : &{x : A & B x}) *)
(*         (f : A -> A') (g : forall x : &{x : A & B x}, B' (f (x.1))) *)
(*         (H : x = y) : *)
(*   f_equal pr1 (sigma_sigma_eq_1 (f_equal (fun x => &(f x.1 & g x)) H) = *)
(*   f_equal (fun x => f x.1) H. *)
(*   Proof. destruct H. simpl. reflexivity. Defined. *)
Polymorphic
  Lemma rewrite_prod {A} {x y z : A} {G : x = y -> Type} (eq : z = y) :
    (forall e : x = z, G (eq_rect z (fun w => x = w) e y eq)) ->
    (forall e : x = y, G e).
  Proof. destruct eq; auto. Defined.


Definition sigma_eq_2_f  {A A'} {B : A' -> Type} {f : A -> A'} {x y : &{ x : A & B (f x) }} : (x = y) -> (&(f x.1 & x.2) = &(f y.1 & y.2)).
Proof.
  destruct x, y. simpl.
  intros H.
  apply sigma_eq_decomp. simpl.
  apply sigma_eq_decomp_inv in H as [H1 H2]. simpl in *.
  exists (f_equal f H1). simpl. destruct H1. simpl in *. exact H2.
Defined.


Notation " 'rew' H 'in' c " := (@eq_rect _ _ _ c _ H) (at level 20).

Definition J {A} {x : A} (P : forall y : A, x = y -> Type)
           (p : P x eq_refl) (y : A) (e : x = y) : P y e.
  destruct e. exact p.
Defined.

Require Import Utf8.

Lemma J_on_refl {A} (x y : A) (e : x = y) : J (λ (y : A) _, x = y) eq_refl y e = e.
Proof. destruct e. constructor. Defined.

Definition subst {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  J (fun x _ => P x) f y e.

Definition subst2 {A : Type} {x : A} {P : A -> Type} (f : P x) (y : A) (e : x = y) : P y :=
  J (fun x _ => P x) f y e.

Definition cong {A B : Type} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
  J (fun y _ => f x = f y) (@eq_refl _ (f x)) y e.
(* aka ap *)

Lemma cong_iter {A B C} (f : A -> B) (g : B -> C) (x y : A) (e : x = y) :
  Top.cong g (Top.cong f e) = Top.cong (fun x => g (f x)) e.
Proof. revert y e. refine (J _ _). reflexivity. Defined.

Notation " 'rew' H 'in' c " := (@subst _ _ _ _ H c) (at level 20).

Notation "p =_{ P ; e } q" := (subst (P:=P) e p = q) (at level 90, format "p  =_{ P ; e }  q").

Definition subst_expl {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  subst e f.
Notation " 'rewP' H 'at' P 'in' c " := (@subst_expl _ _ P _ H c) (at level 20).

Polymorphic Record Equiv (A B : Type) := { equiv :> A -> B ; is_equiv :> IsEquiv equiv }.
Arguments equiv {A B} e.

Polymorphic Instance Equiv_IsEquiv {A B} (e : Equiv A B) : IsEquiv (equiv e).
Proof. apply is_equiv. Defined.

Definition inv_equiv {A B} (E: Equiv A B) : B -> A :=
  equiv_inv (IsEquiv:=is_equiv _ _ E).

Polymorphic Definition equiv_inv_equiv {A B} {E: Equiv A B} (x : A) : inv_equiv _ (equiv E x) = x :=
  eissect x.
Definition inv_equiv_equiv {A B} {E: Equiv A B} (x : B) : equiv E (inv_equiv _ x) = x := eisretr x.
Definition equiv_adj {A B} {E: Equiv A B} (x : A)
  : inv_equiv_equiv (equiv E x) = cong (equiv E) (equiv_inv_equiv x)
  := eisadj x.

Notation " X <~> Y " := (Equiv X Y) (at level 90, no associativity, Y at next level).

Definition equiv_id A : A <~> A.
Proof.
  intros.
  refine {| equiv a := a |}.
  unshelve refine {| equiv_inv e := e |}.
  - red. reflexivity.
  - red; intros. reflexivity.
  - intros. simpl. reflexivity.
Defined.

Axiom axiom_triangle : forall {A}, A.

Definition equiv_sym {A B} : A <~> B -> B <~> A.
Proof.
  intros.
  refine {| equiv a := inv_equiv X a |}.
  unshelve refine {| equiv_inv e := equiv X e |}.
  - red; intros. apply eissect.
  - red; intros. apply eisretr.
  - intros x. simpl. destruct X. simpl. unfold inv_equiv. simpl.
    apply axiom_triangle.
Defined.
Axiom cheat : forall {A}, A.
Lemma isEquiv_cong {A B : Type} (f : A -> B) :
  IsEquiv f -> forall x y, IsEquiv (@cong _ _ f x y).
Proof.
  intros He.
  intros x y.
  unshelve econstructor.
  intros H. apply (cong equiv_inv) in H.
  rewrite !eissect in H. apply H.
  red. intros. unfold eq_ind. unfold equiv_inv. destruct He.
  apply cheat.
  apply cheat.
  apply cheat.
Defined.

Definition sigma_eq_2_f_inv  {A A'} {B : A' -> Type} {f : A -> A'}
           {fequiv : IsEquiv f}
           {x y : &{ x : A & B (f x) }} : (&(f x.1 & x.2) = &(f y.1 & y.2)) -> (x = y).
Proof.
  intros. apply sigma_eq_decomp_inv in H.
  apply sigma_eq_decomp. simpl in *. destruct H.
  revert pr2.
  pose proof (isEquiv_cong f fequiv x.1 y.1).
  simpl in *. pose proof (eisretr (IsEquiv := X) pr1).
  rewrite <- H.
  exists (equiv_inv pr1). clear -pr2.
  revert pr2.
  generalize (equiv_inv pr1). destruct y.
  simpl. intros <-. trivial.
Defined.

Lemma Equiv_cong {A B : Type} (e : Equiv A B) : forall x y : A, Equiv (x = y) (equiv e x = equiv e y).
Proof.
  unshelve econstructor. intros H.
  apply (f_equal (equiv e) H). apply isEquiv_cong. apply e.
Defined.

Definition square {Δ : Type} {w x y z : Δ}
           (t : w = x) (b : y = z) (l : w = y) (r : x = z) : Type :=
  subst (P:=fun x : Δ => x = y) t l =_{fun y : Δ => x = y;b}  r.

Definition flip_square {A} {w x y z} {t b l r} (s : @square A w x y z t b l r) : square l r t b.
Proof.
  revert x t b l r s.
  refine (J _ _). revert z. refine (J _ _).
  intros l r s. unfold square in s. simpl in s.
  revert r s. refine (J _ _).
  revert y l. refine (J _ _).
  unfold square. unfold subst. simpl. reflexivity.
Defined.

Lemma equiv_cong_subst {A B} (P : B -> Type) (f : A -> B)
      (s t : A) (e : s = t) (u : P (f s))
      (v : P (f t)) : u =_{(fun x => P (f x)); e} v <~> (u =_{P; Top.cong f e} v).
Proof.
  unfold Top.subst.
  destruct e. simpl. apply equiv_id.
Defined.

Polymorphic
  Lemma f_equal_inv' {A} {B : Type} (a b : A -> B) (u v : A)
        (r : a u = b u)
        (s : a v = b v)
        (e : u = v)
        (e' : rewP s at (fun x => b u = x) in
            (rewP r at (fun x => x = a v) in
                (cong a e : a u = a v)) = cong b e) :
   rewP cong a e at (fun x => x = b u) in r =_{λ y : B, a v = y;cong b e} s.
  Proof.
    intros.
    unfold subst_expl in e'.
    apply flip_square in e'. red in e'. apply e'.
  Defined.

Polymorphic
  Lemma f_equal_inv2 {A} {B : Type} (a b : A -> B) (u v : A)
        (r : a u = b u)
        (s : a v = b v)
        (e : u = v)
        (e' : rewP cong a e at (fun x => x = b u) in r =_{λ y : B, a v = y;cong b e} s) :
  rewP s at (fun x => b u = x) in
      (rewP r at (fun x => x = a v) in
          (cong a e : a u = a v)) = cong b e.
  Proof.
    intros.
    unfold subst_expl in e'.
    apply flip_square in e'. red in e'. apply e'.
  Defined.

Polymorphic
  Lemma f_equal_inv {A} {B : Type} (a b : A -> B) (u v : A)
        (r : a u = b u)
        (s : a v = b v)
        (e : u = v)
        (e' : rewP s at (fun x => b u = x) in
            (rewP r at (fun x => x = a v) in
                (cong a e : a u = a v)) = cong b e) :
  &(u & r) = &(v & s) :> &{ x : A & a x = b x }.
  Proof.
    intros.
    unfold subst_expl in e'.
    apply flip_square in e'. red in e'.
    destruct e. simpl in *. destruct e'. reflexivity.
  Defined.

  Lemma f_equal_inv_pack {A} {B : Type} (a b : A -> B)
        (x y : &{ x : A & a x = b x })
        (e : x.1 = y.1)
        (e' : rewP y.2 at (fun z : B => b x.1 = z) in
            (rewP x.2 at (fun z : B => z = a y.1) in
                ((cong a e) : a x.1 = a y.1)) = cong b e) :
    x = y.
  Proof.
    intros.
    apply (f_equal_inv a b x.1 y.1) in e'. destruct x, y; auto.
  Defined.

  Lemma pack_f_equal {A} {B : A -> Type} (x : A) (p q : B x) (f : A -> A)
        (G : forall (e : &(x & p) = &(x & q)) (e' : eq_refl = f_equal (fun x => f x.1) e), Type) :
    (forall (e : &(x & p) = &(x & q))
            (e' : f_equal (fun x => f x.1) eq_refl = f_equal (fun x => f x.1) e), G e e') ->
    (forall (e : &(x & p) = &(x & q)) (e' : eq_refl = f_equal (fun x => f x.1) e), G e e').
  Proof. intros. simpl in *. apply X. Defined.

  Polymorphic Definition sigma_eq_2' {A} {B : A -> Type} {x y : &{ x : A & B x }} :
  forall e : x = y, (@eq_rect A x.1 B x.2 y.1 (cong pr1 e)) = y.2.
 Proof.
  destruct e. reflexivity.
Defined.

Lemma rew_cong' {A B} (f : A -> B) (x y : A) (e : x = y)  : rewP e at (fun z => eq (f z) (f y)) in cong f e = eq_refl.
  destruct e. simpl. reflexivity.
Defined.
  Lemma rew_cong {A B} (f : A -> B) (x y : A) (e : x = y)  : (rew cong f e in (@eq_refl B (f x))) = cong f e.
  Proof. destruct e. reflexivity. Defined.

Polymorphic
Definition ind_pack_eq_inv {A : Type}
  {B : A -> Type} (x y : A) (p : B x) (q : B y)
  (e : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
  (i : @eq A x y)
  (ee : rewP e at (fun z => eq z.1 y) in i = eq_refl) :
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
          opaque_ind_pack_eq_inv i G exp ee) ->
  (forall e : p =_{B;i} q, G e).
Proof.
  intros H. intros e.
  specialize (H (make_sigma_eq i e)). unfold opaque_ind_pack_eq_inv in H.
  destruct i, e. simpl in H. specialize (H eq_refl). simpl in G. apply H.
Defined.
Arguments simplify_ind_pack : simpl never.


Polymorphic
Definition ind_pack_eq_inv_cong {A : Type}
  {B : A -> Type} (x y : A) (p : B x) (q : B y)
  (e : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
  (i : @eq A x y)
  (ee : rewP cong (fun x => x.1) e at (fun z => eq z y) in i = eq_refl) :
  rew i in p = q.
Proof.
  revert i ee. change y with (@sigmaI A (fun x => B x) y q).1 at 1 3 4 8 9.
  unfold subst_expl.
  change q with (@sigmaI A (fun x => B x) y q).2 at 10.
  set (s :=@sigmaI A (fun x => B x) y q) in *. clearbody s. destruct e.
  simpl. intros i e. symmetry in e. destruct e. reflexivity.
Defined.

Polymorphic
Lemma simplify_ind_pack_cong {A : Type}
  (B : A -> Type) (x y : A) (p : B x) (q : B y) (i : x = y)
  (G : p =_{B;i} q -> Type) :
  (forall (exp : @eq (sigma A (fun x => B x)) &(x & p) &(y & q))
          (ee : rewP cong pr1 exp at (fun z => eq z y) in i = eq_refl),
           G (@ind_pack_eq_inv_cong A B x y p q exp i ee)) ->
  (forall e : p =_{B;i} q, G e).
Proof.
  intros H. intros e.
  specialize (H (make_sigma_eq i e)). unfold opaque_ind_pack_eq_inv in H.
  destruct i, e. simpl in H. specialize (H eq_refl). simpl in G. apply H.
Defined.
Arguments simplify_ind_pack : simpl never.

(* Lemma pr1_pack_sigma_eq : ∀ (A : Type) (P : A → Type) (p q : A) (x : P p) (y : P q) (e1 : p = q) *)
(*                             (e2 : rew e1 in x = y), cong' pr1 (pack_sigma_eq e1 e2) = e1. *)
(* Proof. *)
(*   intros. destruct e1. destruct e2. simpl. reflexivity. *)
(* Defined. *)

Lemma sigma_eq_1_pack_sigma_eq : ∀ (A : Type) (P : A → Type) (p q : A) (x : P p) (y : P q) (e1 : p = q)
                            (e2 : rew e1 in x = y), sigma_eq_1 (pack_sigma_eq e1 e2) = e1.
Proof.
  intros. destruct e1. destruct e2. simpl. reflexivity.
Defined.

Polymorphic Definition pack_sigma_eq_cong {A} {x y : A} (f : A -> A)
            (e : x = y)
            {e' : f x = f y}
            (e'' : cong f e = e') :
  { a : @sigmaI _ (fun x => f x = f y) x (cong f e) = &(y & eq_refl) &
    sigma_eq_1 a = e }.
Proof. destruct e. destruct e''. simpl. exists eq_refl. apply eq_refl. Defined.

Lemma apply_equiv_dom {A B} (P : A -> Type) (e : Equiv A B) :
  (forall x : B, P (inv_equiv e x)) -> forall x : A, P x.
Proof.
  intros. specialize (X (equiv e x)).
  rewrite equiv_inv_equiv in X. exact X.
Defined.

Set Primitive Projections.
Record pair (A B : Type) := mkPair { fst : A; snd : B }.
Arguments mkPair {A B}.
Arguments fst {A B}.
Arguments snd {A B}.

Derive NoConfusion for pair.
Next Obligation.
  destruct a, b. simpl in H.
  red in H. revert H. simplify *. reflexivity.
Defined.

Definition NoConfVec {E A n} (v v' : Vec E A n) : Type :=
  match v in Vec _ _ n return Vec E A n -> Type with
  | nil => fun v' =>
             match v' in Vec _ _ _ return Type with
             | nil => True
             | cons _ _ => False
             end
  | @cons _ _ n' x xs => fun v' =>
                           match v' in Vec _ _ n'' return
                                 match n'' with
                                 | O => Type
                                 | S n'' => Vec E A n'' -> Type
                                 | E => Type
                                 end with
                       | nil => False
                       | @cons _ _ n'' x' xs' => fun xs => mkPair x xs = mkPair x' xs'
                       end xs
  end v'.

Definition noConfVec_eq {E A n} (v v' : Vec E A n) : v = v' -> NoConfVec v v'.
Proof.
  intros ->. destruct v'. constructor. simpl. constructor.
Defined.

Definition vnil_elim {E A} (P : Vec E A O -> Type) (v : P nil) : forall v, P v.
Proof.
  intros.
  refine (match v0 as v' in Vec _ _ n' return
                match n' return Vec E A n' -> Type with
                | O => fun v' => P v'
                | _ => fun _ => True
                end v'
          with
          | nil => _
          | cons _ _ => I
          end). exact v.
Defined.

Definition vcons_elim {E A} (P : forall n, Vec E A (S n) -> Type) (H : forall n a (v' : Vec E A n), P n (cons a v')) : forall n v, P n v.
Proof.
  intros.
  refine (match v as v' in Vec _ _ n' return
                match n' as n'' return n' = n'' -> Vec E A n' -> Type with
                | O => fun _ _ => True
                | S n' => fun H v => P _ (rew H in v')
                | raise _ _ => fun _ _ => True
                end eq_refl v'
          with
          | nil => I
          | cons a v' => H _ a v'
          end).
Defined.

Definition noConfVec_eq_inv {E A n} (v v' : Vec E A n) : NoConfVec v v' -> v = v'.
Proof.
  destruct v. simpl.
  revert v'. refine (vnil_elim _ _). intros. constructor.
  revert n v' v. refine (vcons_elim _ _).
  simpl. intros. change a with ((mkPair a v').(fst)). change v' with ((mkPair a v').(snd)) at 2.
  destruct H. reflexivity.
Defined.

Lemma noConfVec_eq_eq_inv {E A n} (v v' : Vec E A n) (e : v = v') :
  noConfVec_eq_inv _ _ (noConfVec_eq _ _ e) = e.
Proof.
  destruct e. destruct v. unfold noConfVec_eq_inv. simpl. reflexivity.
  simpl. unfold eq_ind_r, eq_ind. simpl. reflexivity.
Defined.

Lemma noConfVec_refl {E A n} (v : Vec E A n) : NoConfVec v v.
Proof. destruct v. reflexivity. reflexivity. Defined.

Lemma noConfVec_eq_inv_eq_refl {E A n} (v : Vec E A n) :
  noConfVec_eq _ _ (noConfVec_eq_inv v v (noConfVec_refl v)) = (noConfVec_refl v).
Proof.
  destruct v. reflexivity. reflexivity.
Defined.

Lemma noConfVec_eq_inv_eq {E A n} (v v' : Vec E A n) (e : NoConfVec v v') :
  noConfVec_eq _ _ (noConfVec_eq_inv _ _ e) = e.
Proof.
  destruct v. revert v' e. refine (vnil_elim _ _). simpl. destruct e. reflexivity.
  revert n v' v e. refine (vcons_elim _ _). intros.
  simpl in e.
  simpl.
  change a with (mkPair a v').(fst) at 1 2. change v' with (mkPair a v').(snd) at 2 4.
  revert e. generalize (mkPair a v'). intros p e. destruct e. reflexivity.
Defined.

Definition noConf_vec_equiv {E A n} (v v' : Vec E A n) : Equiv (v = v') (NoConfVec v v').
Proof.
  refine {| equiv := noConfVec_eq v v' |}.
  unshelve refine {| equiv_inv := noConfVec_eq_inv v v' |}.
  red. intros.
  apply noConfVec_eq_inv_eq.
  red; intros.
  apply noConfVec_eq_eq_inv.
  intros ->.
  destruct v'. simpl. reflexivity.
  simpl. reflexivity.
Defined.

Definition vector_args_type {A} {E} (n : ℕ E) (v : Vec E A n) : Type :=
  match v with
  | nil => unit
  | @cons _ _ n' a v => &{ n : _ & &{a : A & Vec E A n }}
  end.

Definition vector_args {A} {E} (n : ℕ E) (v : Vec E A n) : vector_args_type n v :=
  match v as v' in Vec _ _ n return vector_args_type n v' with
  | nil => tt
  | @cons _ _ n a v => &(n, a & v)
  end.

Definition apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  rew p in f x = f y.
Proof. destruct p; reflexivity. Defined.

Set Nested Proofs Allowed.

(* Definition cong {A B : Type} (f : A -> B) {x y : A} (e : x = y) : f x = f y := *)
(*   J (fun y _ => f x = f y) (@eq_refl _ (f x)) y e. *)

Inductive sig_eq {A : Type} {B : A -> Type} (x : &{ x : A & B x }) : forall y : &{ x : A & B x }, x = y -> Prop :=
  sig_eq_refl : sig_eq x x eq_refl.

Inductive is_refl {A : Type} {x : A} : forall {y : A}, x = y -> Prop :=
  is_refl_refl : is_refl eq_refl.

Lemma is_refl_refl' {A : Type} {x : A} (p : x = x) : is_refl p -> p = eq_refl.
Proof.
  intros H.
  generalize_eqs_sig H.
  destruct H. simpl.
  intros.
  pose (apd (A:=sigma A (fun y : A => x = y)) (fun x => pr2 x) H).
  simpl in e. rewrite <- e. clear.
  revert x p H.

  Lemma eq_subst {A} : ∀ (x y : A) (p : x = y) (H : y = y) (prf : eq_refl = H),
      p = rewP H at (fun y => eq x y) in p.
  Proof. intros. destruct p. destruct prf. reflexivity. Qed.
  intros.
  pose (cong (A:=sigma A (fun y : A => x = y)) (fun x => pr1 x) H).
  simpl in e.
Admitted.

Lemma sig_eq_pr1 {A : Type} {B : A -> Type} (x : A) (p : B x) (q : B x)
      (e : x = x) (e' : rew e in p = q) : sig_eq _ _ (pack_sigma_eq e e') -> e = eq_refl.
Proof.
  destruct e'.
  intros.
  generalize_eqs_sig H.
  destruct H. simpl.
  intros.
  pose (apd (A:=(sigma (sigma A (fun x : A => B x))
                       (fun y : sigma A (fun x : A => B x) => @eq (sigma A (fun x : A => B x)) (@sigmaI A B x p) y))
            ) (fun x => pr2 x) H). simpl in e0.
  pose (apd (A:=@eq (sigma A (fun x : A => B x)) (@sigmaI A B x p) (@sigmaI A B _ _))
            (fun x => sigma_eq_1 x) e0).
  simpl in e1. rewrite <- e1.
  clear e1.
  subst e0.

  (* Lemma sigma_eq_1_rew {A : Type} {B : A -> Type} (x : A) (p : B x) (q : B x) *)
  (*     (e : x = x) (e' : rew e in p = q) (H :  : sigma_eq_1 (rew H in pack_sigma_eq e e'). *)
Admitted.

Lemma cong_f {A B} (f : A -> B) (g : B -> A)
      (retr : forall x, g (f x) = x)
      (x y : A) (e : x = y) (e' : f x = f y) :
  (forall e' : f x = f x, cong (fun x => f (g x)) e' = eq_refl -> eq_refl = e') ->

  (cong f e = e') <~>
  (rewP retr x at (fun z => z = y) in (rewP (retr y) at (fun z => g (f x) = z) in cong g e') = e).
Proof.
  intros Hc.
  destruct e. simpl in *.
  unfold subst_expl. unfold subst.
  destruct (retr x). simpl.
  unshelve econstructor. intros H.
  destruct H. reflexivity.
  unshelve econstructor. intros H.
  apply (cong (cong f)) in H.
  revert H.
  rewrite cong_iter. simpl.
  apply Hc.
  red. intros. unfold eq_ind_r. unfold cong_iter. simpl.
  unfold eq_sym, J, eq_ind.
  apply cheat.
  red. intros. apply cheat. apply cheat.

Defined.

  Definition eq_fn {A B} (e : A = B) : A -> B.
    destruct e. exact id.
  Defined.

(* Lemma apply_eq_dom {A B : Type} (P : B -> Type) (e : A  B) : *)
(*   (forall x : A, P (eq_fn e x)) -> forall x : B, P x. *)
(* Proof. *)
(*   intros. destruct e. apply X. Defined. *)

Lemma cong_f_inj {A B} (f : A -> B) (g : B -> A)
      (retr : forall x y, f x = f y -> x = y)
      (x y : A) (e e' : x = y) :
  cong f e = cong f e' -> e = e'.
Proof.
  intros.
Admitted.

Polymorphic Definition sigma_eq_2'' {A} {B : A -> Type} {x y : &{ x : A & B x }} :
  forall e : x = y, (@eq_rect A x.1 B x.2 y.1 (cong pr1 e)) = y.2.
 Proof.
  destruct e. reflexivity.
Defined.

Definition vect_hd {A E n} (v : Vec A E (S n)) :=
  match v with
  | cons a' v' => a'
  end.

Definition vect_tl {A E n} (v : Vec A E (S n)) :=
  match v with
  | cons a' v' => v'
  end.

Polymorphic
  Lemma f_equal_inv_dep {A} {B : Type} (a b : A -> B) (u v : A)
        (e : u = v)
        (r : u = v -> a u = b u)
        (s : a v = b v)
        (H : rewP e at (fun x => a x = b x) in r e = s :> (a v = b v)) :
  rewP s at (fun x => b u = x) in
    (rewP (r e) at (fun x => x = a v) in
        (cong a e : a u = a v)) = cong b e.
  Proof.
    intros.
    unfold subst_expl in H.
    apply flip_square.
    destruct e. simpl in *. destruct H. reflexivity.
  Defined.

 Equations param_vector_vcons E (A : Set) (a : A) (n : ℕ E) (v : Vec E A n)
          (X : vector_param E A (S n) (cons a v)) : vector_param E A n v :=
  param_vector_vcons E A _ _ _  (vcons_param _ _ _ X) := X.
Transparent param_vector_vcons.
Next Obligation.
  generalize_eqs_sig X.
  destruct X.
  simplify ?. simpl.
  refine (eq_simplification_sigma1_dep_dep _ _ _ _ _).
  refine (eq_simplification_sigma1_dep_dep (S n) (S n0) (cons a v) (cons a0 v0) _).
  simplify ?.
  simplify ?.
  simpl noConfusion_inv.
  simpl.
  refine (apply_equiv_dom _ (noConf_vec_equiv _ _) _).
  simpl.
  simplify ?.
  simplify ?.
  simplify ?.
  simplify ?.
  simpl.
  constructor.
Defined.


  Transparent pack_sigma_eq.
  Lemma cong_pack (A : Type) (P : A → Type) (B : A -> Type) (x y : A) (p : P x) (q : P y)
        (e : x = y) (e' : rew e in p = q)
        (f : A -> A) (g : forall x, P x -> B (f x)) :
    &{ e'' : _ &
    cong (fun x => &(f x.1 & g x.1 x.2)) (pack_sigma_eq e e') =
    pack_sigma_eq (cong f e) e'' }.
  Proof.
    unshelve eexists. simpl. destruct e. simpl. destruct e'. simpl. reflexivity.
    destruct e, e'. simpl. reflexivity.
  Defined.

  unshelve evar(He' : (eq_refl = e') <~> (cong pr1 (cong cf (pack_sigma_eq e' e)) = eq_refl)).
  destruct (cong_pack _ _ (fun x => Vec E A x) n0 n0 _ _ e' e (fun x => S x) (fun x y => cons y.1 y.2))
    as [He'' Hpack].
  rewrite Hpack. rewrite pr1_pack_sigma_eq.
  clear He'' Hpack.

  unshelve econstructor. intros <-. reflexivity.
  unshelve econstructor.
  intros. symmetry.
  change eq_refl with (@cong _ _ (fun x : ℕ E => S x) n0 n0 eq_refl) in H.

  Lemma cong_eq_inj {A B} (x y : A) (e e' : x = y) (f : A -> B) (g : B -> A) : cong f e = cong f e' -> e = e'.
  Proof. intros He.
         apply (cong (cong g)) in He.

  specialize (f_equal_inv'
                (fun x => S x) (fun _ => S n0) n0 n0 eq_refl eq_refl e'). simpl.
  rewrite H. simpl.

  rewrite rew_cong.


  set (g := (fun x => match x return ℕ E with S x => x | _ => x end)).
  unshelve evar(retr : forall x, g (S x) = x).
  intros. unfold g. reflexivity.
  pose (cong_f (fun x => S x) g retr _ _ e' eq_refl). simpl in e0.
  forward e0. simpl. intros.

  Lemma cong_id {A} (f g : A -> A) (x y : A) (e : x = y)
    (ex : x = f (g x)) (ey : y = f (g y)) :
    cong (fun x => f (g x)) e =
    rewP ex at (fun z => z = f (g y)) in rewP ey at (fun z => x = z) in e.
  Proof.
    destruct e. simpl. destruct ex. simpl. apply cheat.
  Defined.

  unshelve erewrite cong_id in H. simpl. reflexivity. simpl. reflexivity.
  simpl in H. symmetry in H. apply H.

  apply (equiv_sym e0).


  refine (apply_equiv_dom _ He _).
  intros x. destruct x.
  subst He. simpl.
  revert e. simpl.
  simplify ?.
  simplify ?. simpl.
  Transparent pack_sigma_eq. simpl.
  unfold ind_pack_eq_inv. simpl. unfold inv_equiv. simpl.
  unfold eq_ind_r. simpl. unfold eq_ind. unfold eq_sym. simpl.

  apply cheat. Defined.
  simplify ?. simpl.
  simplify ?. simpl.
  constructor.
Defined.

  unfold ind_pack_eq_inv. unfold sigma_eq_2'.
  unfold

  pose proof (eq_sym (cong_iter cf pr1 _ _ match e in (_ = y) return (&(n0, a & v) = &(n0 & y)) with
                                           | eq_refl => eq_refl
                                           end)).

  refine (@apply_equiv_dom (cong (λ x : &{ n : ℕ E & &{ _ : A & Vec E A n}}, (cf x).1)
        match e in (_ = y) return (&(n0, a & v) = &(n0 & y)) with
        | eq_refl => eq_refl
        end) _ H _).




  rewrite H0 in ee.
  specialize (f_equal_inv' (fun x => (cf x).1) (fun _ : &{ n : ℕ E & &{ _ : A & Vec E A n}} => S n0)
                           &(n0, a & v) &(n0, a0 & v0) eq_refl eq_refl H ee).
  simpl. unfold subst_expl. subst cf. simpl.
  simpl in *.
  intros. apply H1.
  subst x.
  revert H ee X1. subst cf.
  intros H ee X1. revert ee.
  unfold ind_pack_eq_inv.
  revert H X1.
  refine (eq_simplification_sigma1_dep_dep _ _ _ _ _).
  intros.

  pose proof (rew_cong (λ x : &{ n : ℕ E & &{ _ : A & Vec E A n}}, S x.(pr1)) _ _ (pack_sigma_eq e' e)).
  simpl in H0.
  revert X1.
  match goal with
    |- ?X =_{_;_} _ -> _ => set (foo:=X)
  end.
  replace foo
    with (cong (λ x : &{ n : ℕ E & &{ _ : A & Vec E A n}}, S x.(pr1)) (pack_sigma_eq e' e)).
  intros.
  2:{ subst foo. rewrite <- H0 at 1. admit. }



  subst cf.
  assert (&{n : ℕ E & &{ _ : A & &{ _ : Vec E A n0 & S n = S n}}} <~>
          &{n : ℕ E & &{ _ : A & &{ _ : Vec E A n0 & S n0 = S n0}}}).
  unshelve econstructor. intros [n [a' [v' e']]]. exists n. exists a. exists v'. reflexivity.
  unshelve econstructor. intros [n [a' [v' e']]]. exists n. exists a. exists v'. reflexivity.
  red. intros [n [a' [v' e']]]. admit. admit. admit.
  pose proof (is_equiv _ _ X2).
  pose (@isEquiv_cong _ _ _ X2 &(n0, a, v & eq_refl) &(n0, a0 , v0 & eq_refl)).
  pose (f_equal X2 (x:=&(n0, a0, v0 & eq_refl)) (y:=&(n0, a0, v0 & eq_refl))).
  pose (@isequiv _ _ _ i). simpl in e.



  destruct (pack_sigma_eq_cong _ e' ee). as [e'0 ee'0]. revert ee'.

  destruct ee'0.
  unshelve evar (equi : &{ x : ℕ E & S x = S n0} <~> ()).
  unshelve econstructor. exact (fun _ => tt). unshelve econstructor.
  intros. exists n0. reflexivity. red. destruct x. auto.
  red. intros [x Heq]. revert Heq. simplify *. reflexivity.
  admit.
  revert e'0.
  epose (apply_equiv_dom _ (equiv_sym e)).
  refine (y _). simpl.
  intros Hx. clear y.
  assert (sigma_eq_1 (inv_equiv e Hx) = eq_refl).
  subst e.
  unfold Equiv_cong. simpl. unfold inv_equiv.
  unfold equiv_inv;simpl.
  unfold sigma_eq_1. simpl. unfold pack_sigma_eq. simpl.
  unfold eq_ind. simpl. unfold apply_noConfusion. simpl.
  unfold noConfusion_ℕ_obligation_3. simpl.
  unfold noConfusion_ℕ_obligation_1. simpl.
  unfold cong. simpl.
  unfold inv_equiv_equiv





  simpl.
  simpl.
  specialize (i &(n0 & cong S e') &(n0 & eq_refl)).
  revert i.
  match goal with
  pattern (f_equal _). (λ _ : &{ x : ℕ E & S x = S n0}, ())
                                (x := &(n0 & cong (λ x : ℕ E, S x) e'))
                                (y:=&(n0 & eq_refl))).
  destruct i. pose (equiv_inv0 eq_refl).
  red in eissect0.






  change eq_refl with (cong (fun x => S x) (@eq_refl _ n0)) in ee'.
  unfold subst_expl in e0. simpl in e0. simpl in ee'.
  eq_refl eq_refl e'). simpl in e0.
  (* eq_refl (cong (fun x : ℕ E => S x) e') eq_refl eq_refl). *)
  simpl in e0. unfold subst_expl in e0.
  rewrite cong_p

  simpl in ee'.

  rewrite



  pose (f_equal_inv_pack (A := ℕ E)
                               (fun x => S x)
                               (fun x => S x)).
  simpl in e. specialize (e &(n0 & eq_refl)).
  simpl in e.
  intros H.
  unshelve epose proof (e &(n0 & _)).
  simpl. exact (cong
                                  (λ j : &{ n : ℕ E & &{ _ : A & Vec E A n}},
                                         (S j.(pr1))) H).
  simpl in H0. specialize (H0 eq_refl). simpl in *.

  forward H0.
  unfold subst_expl.

  simpl in H0.


  pose (f_equal_inv_pack (A := &{ n0 : _ & &{ a : A & Vec E A n0 }})
                               (fun x => S x.1)
                               (fun x => S x.1)).
  simpl in e. specialize (e &( &(n0, a & v) & eq_refl)).
  simpl in e.
  intros H.
  unshelve epose proof (e &(&(n0, a0 & v0) & _)).
  simpl. exact (cong
                                  (λ j : &{ n : ℕ E & &{ _ : A & Vec E A n}},
                                         (S j.(pr1))) H).
  simpl in H0. specialize (H0 H). clear e.
  forward H0.
  unfold subst_expl.

  simpl in H0.

                         )).
  refine pack_f_equal.


  assert (f_equal pr1
           (f_equal
              (fun x : &{ n : ℕ E & &{ _ : A & Vec E A n}} =>
                 &(S x.(pr1) & cons x.(pr2).(pr1) x.(pr2).(pr2))) H)
          = f_equal (fun x : &{ n : ℕ E & &{ _ : A & Vec E A n}} => S x.(pr1)) H).
  destruct H. reflexivity. symmetry in H0.
  refine (rewrite_prod H0 _).

  intros H'. revert H0.
  revert H H'.
  intros H.
  change (@eq_refl _ (S n0)) with (f_equal (fun x : &{ n : ℕ E & &{ _ : A & Vec E A n}} => S x.1) (@eq_refl _ &(n0, a & v))) at 1.
  revert H.




  unfold opaque_ind_pack_eq_inv.



  pose (sigma_eq_1_f_equal   &(n0, a & v) &(n0, a0 & v0) (fun x => S x) (fun x => cons x.2.1 x.2.2) H).
  simpl in e. symmetry in e.
  refine (rewrite_prod e _).




  unfold f_equal at 2. simpl

  unfold opaque_ind_pack_eq_inv. simpl.


  simpl in e0.
  
(* Polymorphic *)
(* Definition sigma_eq_2_cong_gl  {A} {B : A -> Type} {f : A -> A} {x y : &{ x : A & B (f x) }} *)
(*   (G : &(f x.(pr1) & x.(pr2)) = &(f y.(pr1) & y.(pr2)) -> Type) : *)
(*   forall (e : @eq (sigma A (fun x => B (f x)) &(x & p) = &(y & q)))
(*     G e.
(*   ), *)
(*   forall (e : @eq (sigma A (fun x => B x) &(f x & p) = &(f y & q)))
(*     G e.

(* Proof. *)
(*   destruct e. reflexivity. *)
(* Defined. *)

  simplify ?. simpl.

  Polymorphic Lemma eq_simplification_sigma1_dep_dep_inv {A} {P : A -> Type}
  (x y : A) (p : P x) (q : P y) {B : &(x & p) = &(y & q) -> Type} :
  (forall e : sigmaI P x p = sigmaI P y q, B e).
  (forall e' : x = y, forall e : @eq_rect A x P p y e' = q, B (pack_sigma_eq e' e)) ->
Proof.
  intros. revert X.
  change x with (pr1 &(x & p)).
  change y with (pr1 &(y & q)).
  change p with (pr2 &(x & p)) at 3 5.
  change q with (pr2 &(y & q)) at 4 6.
  destruct e.
  intros X. simpl in *.
  apply (X eq_refl eq_refl).
Defined.



  refine (eq_simplification_sigma1_dep_dep _ _ _ _ _).
  intros e'.
  refine (simplify_ind_pack _ _ _ _ _ _).


Defined.

  simplify ?.


  constructor.
Defined.
