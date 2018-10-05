From Equations Require Import Equations DepElimDec HSets.

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

Definition sigma_eq_decomp_inv {A} {B : A -> Type} {x y : sigma A B} :
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

Axiom cheat : forall {A}, A.
Lemma isEquiv_cong {A B : Type} (f : A -> B) :
  IsEquiv f -> forall x y, IsEquiv (@f_equal _ _ f x y).
Proof.
  intros He.
  intros x y.
  unshelve econstructor.
  intros H. apply (f_equal equiv_inv) in H.
  rewrite !eissect in H. apply H.
  red. intros. unfold eq_ind.
  apply cheat.
  apply cheat.
  apply cheat.
Defined.


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

Polymorphic
Definition ind_pack_eq_inv {A : Type}
  {B : A -> Type} (x : A) (p q : B x) (e : @eq (sigma A (fun x => B x)) &(x & p) &(x & q))
  (e' : eq_refl = f_equal pr1 e) : p = q.
Proof.
  pose proof (sigma_eq_2 e). simpl in H. destruct H. destruct e'. reflexivity.
Defined.

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
Definition opaque_ind_pack_eq_inv {A : Type}
{B : A -> Type} {x : A} {p q : B x} (G : p = q -> Type) (e : &(x & p) = &(x & q))
  (ee : eq_refl = f_equal pr1 e)
  := G (@ind_pack_eq_inv A B x p q e ee).
Arguments opaque_ind_pack_eq_inv : simpl never.

Polymorphic
Lemma simplify_ind_pack {A : Type}
      (B : A -> Type) (x : A) (p q : B x) (G : p = q -> Type) :
  (forall (e : @eq (sigma A (fun x => B x)) &(x & p) &(x & q))
          (ee : eq_refl = f_equal pr1 e),
          opaque_ind_pack_eq_inv G e ee) ->
  (forall e : p = q, G e).
Proof.
  intros H. intros e.
  specialize (H (ind_pack_eq e)). unfold opaque_ind_pack_eq_inv in H.
  destruct e. simpl in H. apply (H eq_refl).
Defined.
Arguments simplify_ind_pack : simpl never.

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


Set Nested Proofs Allowed.
Equations param_vector_vcons E (A : Set) (a : A) (n : ℕ E) (v : Vec E A n)
          (X : vector_param E A (S n) (cons a v)) : vector_param E A n v :=
  param_vector_vcons E A _ _ _  (vcons_param _ _ _ X) := X.
Transparent param_vector_vcons.
Next Obligation.
  generalize_eqs_sig X. destruct X.
  simplify ?. simpl.
  apply eq_simplification_sigma1_dep.
  refine (eq_simplification_sigma1_dep_dep (S n) (S n0) (cons a v) (cons a0 v0) _).
  simplify ?.
  simplify ?.
  simpl.
  refine (simplify_ind_pack _ _ _ _ _ _). simpl.
  simplify ?.
  unfold NoConfusion. unfold NoConfusionPackage_Vec.
  unfold NoConfusion_Vec.
  intros H. simpl in H.
  unfold noConfusion_inv. unfold noConfusion_Vec_obligation_2.
  change (match
             H in (_ = y)
             return (&(S n0 & cons a v) = &(S y.(pr1) & cons y.(pr2).(pr1) y.(pr2).(pr2)))
           with
           | eq_refl => eq_refl
           end) with (f_equal (fun x => &(S x.1 & cons x.2.1 x.2.2)) H).
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


Polymorphic
Definition sigma_eq_2_f  {A A'} {B : A' -> Type} {f : A -> A'} {x y : &{ x : A & B (f x) }} : (x = y) -> (&(f x.1 & x.2) = &(f y.1 & y.2)).
Proof.
  destruct x, y. simpl.
  intros H.
  apply sigma_eq_decomp. simpl.
  apply sigma_eq_decomp_inv in H as [H1 H2]. simpl in *.
  exists (f_equal f H1). simpl. destruct H1. simpl in *. exact H2.
Defined.

Definition sigma_eq_2_f_inv  {A A'} {B : A' -> Type} {f : A -> A'}
           {fequiv : IsEquiv f}
           {x y : &{ x : A & B (f x) }} : (&(f x.1 & x.2) = &(f y.1 & y.2)) -> (x = y).
Proof.
  intros. apply sigma_eq_decomp_inv in H.
  apply sigma_eq_decomp. simpl in *. destruct H.
  revert pr2.
  pose proof (isEquiv_cong f fequiv x.1 y.1).
  simpl in *. pose proof (eisretr (IsEquiv := H) pr1).
  rewrite <- H0.
  exists (equiv_inv pr1). clear -pr2.
  revert pr2.
  generalize (equiv_inv pr1). destruct y.
  simpl. intros <-. trivial.
Defined.

Polymorphic
  Lemma f_equal_inv {A} {B : Type} (a b : A -> B) (u v : A)
        (F : &{ x : A & a x = b x } -> Type)
        (r : a u = b u)
        (s : a v = b v)
        (e : u = v)
        (e' : eq_trans (eq_sym r) (eq_trans (f_equal a e : a u = a v) s) = f_equal b e) :
    (F &(u & r) = F &(v & s)).
  Proof.
    intros.
    pose (@f_equal _ _ F &(u & r) &(v & s)). apply e0. clear e0.

    pose (@make_sigma_eq A (fun x => b u = b x) u v). simpl in e0.
    specialize (e0 (eq_trans (eq_sym r) (eq_trans (f_equal a e) (eq_trans s (f_equal b (eq_sym e))))) (f_equal b e) e). forward e0. apply cheat.
    apply (sigma_eq_2_f (f := fun x => b x)) in e0.
    simpl in *.


    pose proof (sigma_eq_2_cong
                  (A := A) (A' := B) (B := fun y :  => @eq B (a y) (b y))
                  (x := &(u & r)) (y := &(v & s)) (f := fun x : A => a x)
               ). simpl in H.

    aply forward e0.



    destruct s. unfold eq_trans, eq specialize (H x y).
    destruct p. simpl in *. apply


  Lemma pack_f_equal {A} {B : A -> Type} (x : A) (p q : B x) (f : A -> A)
        (G : forall (e : &(x & p) = &(x & q)) (e' : eq_refl = f_equal (fun x => f x.1) e), Type) :
    (forall (e : &(x & p) = &(x & q))
            (e' : f_equal (fun x => f x.1) eq_refl = f_equal (fun x => f x.1) e), G e e') ->
    (forall (e : &(x & p) = &(x & q)) (e' : eq_refl = f_equal (fun x => f x.1) e), G e e').
  Proof. intros. simpl in *. apply X. Defined.
  refine (pack_f_equal _ _ _ _ _ _ _).

  unfold opaque_ind_pack_eq_inv.
  simpl in *.


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
