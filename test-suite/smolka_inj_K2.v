From Equations Require Import Equations. 

Set Equations Transparent.

Inductive K : nat -> nat -> Type :=
| K1:  K x 
| K2: forall y z w, w = y -> K x w -> K y z -> K x z.


Inductive K (x: nat) : nat -> Type :=
| K1 y : S x = y -> K x y
| K2: forall y z w, w = y -> K x w -> K y z -> K x z.

Derive Signature for K.
Derive NoConfusionHom for K.

Inductive K' (x: nat) : nat -> Type :=
| K1' : K' x (S x)
| K2' : forall y z, K' x y -> K' y z -> K' x z.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Equations ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
ap f eq_refl := eq_refl.

Equations ap2 {A B C : Type} (f : A -> B -> C) {x y : A} (p : x = y) {x' y'} (p' : x' = y') : f x x' = f y y' :=
ap2 f eq_refl eq_refl := eq_refl.


Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B}%_type_scope f%_function_scope {_} _.
Arguments eissect {A B}%_type_scope f%_function_scope {_} _.
Arguments eisadj {A B}%_type_scope f%_function_scope {_} _.
Arguments IsEquiv {A B}%_type_scope f%_function_scope.

Equations KK' (x y : nat) (K : K x y) : K' x y :=
KK' x y (K1 _ eq_refl) := K1' x;
KK' x y (K2 _ _ _ eq_refl l r) := K2' _ _ _ (KK' x _ l) (KK' _ _ r).

Equations K'K (x y : nat) (k : K' x y) : K x y :=
K'K x ?(S x) (K1' x) := K1 x (S x) eq_refl;
K'K x y (K2' w y l r) := K2 _ _ _ _ _ (K'K x w l) (K'K w y r).

Equations KK'sect x y : Sect (K'K x y) (KK' x y) :=
KK'sect x ?(S x) (K1' x) := eq_refl;
KK'sect x y (K2' w y l r) := ap2 (K2' x w y) (KK'sect _ _ l) (KK'sect _ _ r).

Equations K'Ksect x y : Sect (KK' x y) (K'K x y) :=
K'Ksect x y (K1 _ eq_refl) := eq_refl;
K'Ksect x y (K2 w y w eq_refl l r) := ap2 (K2 x _ _ _ eq_refl) (K'Ksect _ _ l) (K'Ksect _ _ r).

Lemma ap2_ap {A B C D E} {x y : A} {x' y' : B} {f : C -> D -> E} {g:  A -> C} {h : B -> D} 
  {p : x = y} {q : x' = y'} : 
  ap2 f (ap g p) (ap h q) = ap2 (fun x y => f (g x) (h y)) p q.
Proof.
  now destruct p, q; cbn.
Qed.

Lemma ap_ap2 {A B C D} {x y : A} {x' y' : B} {g : A -> B -> C} {f : C -> D} 
  {p : x = y} {q : x' = y'} : 
  ap f (ap2 g p q) = ap2 (fun x y => f (g x y)) p q.
Proof.
  now destruct p, q; cbn.
Qed.

 (*Lemma ap2_ap_K2' {x y z} {p : K'K x y (KK' x y k1) = k1) q} :
  ap2 (K2' x y z) (ap (KK' x y) p) (ap (KK' y z) q) = ap (KK' x z) (ap2 (x:=) (K2 x y z) p q). *)

Lemma K_equiv x y : IsEquiv (KK' x y).
Proof.
  unshelve eapply (BuildIsEquiv _ _ _ (K'K x y)).
  - apply KK'sect.
  - apply K'Ksect.
  - intros k. induction k; simp KK' KK'sect.
    * destruct e. reflexivity.
    * destruct e. unfold KK' at 4; fold (KK' x w k1). fold (KK' _ _ k2).
      simpl.
      rewrite IHk1, IHk2.
      now rewrite ap2_ap, ap_ap2.
Qed.

Lemma K2_K2'_eq x y (p q : K x y) (H : p = q) : (KK' _ _ p = KK' _ _ q).
Proof.
  destruct H. reflexivity.
Qed.

Derive Signature NoConfusionHom for K'.

Fact K2'_injective x y z a b a' b' :
  K2' x y z a b = K2' x y z  a' b' -> (a,b) = (a',b').
Proof.
  intros h.
  pose proof (ap (K'K _ _) h).
  simp K'K in H.
  noconf H. depelim H.
  cbn in h.

Fact K2_injective x y z w a b a' b' eq eq':
  K2 x y z w eq a b = K2 x y z w eq' a' b' -> (a,b) = (a',b').
Proof.
  intros h.
  pose proof (ap (KK' _ _) h).
  cbn in H.
  apply K_equiv in h.
  intros h%(noConfusionHom_K_obligation_2 _ _).
  simpl in h. depelim h. destruct h1'1. destruct eq.
  destruct h as [yy' [zz' [aa' bb']]].
  rewrite (UIP_refl_nat _ yy') in aa', bb'.
  rewrite (UIP_refl_nat _ zz') in bb'.
  rewrite <- aa', <- bb'.
  reflexivity.
Qed.
