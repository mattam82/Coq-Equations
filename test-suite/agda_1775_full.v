From Equations Require Import Equations DepElimDec HSets.
(* Set Universe Polymorphism. *)
(** Can we define NoConfusion in SProp (squashing equalities of arguments)?
    Would not allow to show equivalence to (x = y) for non-strict sets. *)
Unset Equations WithK.

Import Sigma_Notations.
Open Scope equations_scope.

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
  : inv_equiv_equiv (equiv E x) = f_equal (equiv E) (equiv_inv_equiv x)
  := eisadj x.

Notation " 'rew' H 'in' c " := (@eq_rect _ _ _ c _ H) (at level 20).

Require Import Utf8.

Notation " X <~> Y " := (Equiv X Y) (at level 90, no associativity, Y at next level).

Lemma apply_equiv_dom {A B} (P : A -> Type) (e : Equiv A B) :
  (forall x : B, P (inv_equiv e x)) -> forall x : A, P x.
Proof.
  intros. specialize (X (equiv e x)).
  rewrite equiv_inv_equiv in X. exact X.
Defined.


Inductive fin : nat -> Set :=
| fin0 n : fin (S n)
| finS n : fin n -> fin (S n).
Derive Signature for fin.

Arguments fin0 {_}.
Arguments finS {_} _.

(* Derive NoConfusion for ℕ. *)
Derive NoConfusion for fin.

Equations noConf_fin {n} (v v' : fin n) : Prop :=
noConf_fin fin0 fin0 := True;
noConf_fin (finS f) (finS f') := f = f';
noConf_fin _ _ := False.
Transparent noConf_fin.
Print Assumptions noConf_fin_elim.

Definition noConf_fin_eq {n} (v v' : fin n) : v = v' -> noConf_fin v v'.
Proof.
  intros ->. destruct v'; constructor.
Defined.

Definition noConf_fin_eq_inv {n} (v v' : fin n) : noConf_fin v v' -> v = v'.
Proof.
  funelim (noConf_fin v v'); try simplify *; constructor.
Defined.

Lemma noConf_fin_eq_eq_inv {n} (v v' : fin n) (e : v = v') :
  noConf_fin_eq_inv _ _ (noConf_fin_eq _ _ e) = e.
Proof.
  destruct e. destruct v; reflexivity.
Defined.

Lemma noConf_fin_refl {n} (v : fin n) : noConf_fin v v.
Proof. destruct v; reflexivity. Defined.

Lemma noConf_fin_eq_inv_eq_refl {n} (v : fin n) :
  noConf_fin_eq _ _ (noConf_fin_eq_inv v v (noConf_fin_refl v)) = (noConf_fin_refl v).
Proof.
  destruct v; reflexivity.
Defined.

Lemma noConf_fin_eq_inv_eq {n} (v v' : fin n) (e : noConf_fin v v') :
  noConf_fin_eq _ _ (noConf_fin_eq_inv _ _ e) = e.
Proof.
  destruct v; revert e; depelim v'; simplify *; reflexivity.
Defined.

Lemma noConf_fin_hom_equiv : forall n, NoConfusionPackage (fin n).
Proof.
  unshelve econstructor.
  refine noConf_fin.
  apply noConf_fin_eq.
  apply noConf_fin_eq_inv.
  apply noConf_fin_eq_eq_inv.
Defined.
Existing Instances noConf_fin_hom_equiv.

Definition noConf_fin_equiv {n} (v v' : fin n) : Equiv (v = v') (noConf_fin v v').
Proof.
  refine {| equiv := noConf_fin_eq v v' |}.
  unshelve refine {| equiv_inv := noConf_fin_eq_inv v v' |}.
  red. intros.
  apply noConf_fin_eq_inv_eq.
  red; intros.
  apply noConf_fin_eq_eq_inv.
  simplify *. destruct v'; reflexivity.
Defined.

Inductive Vec (A : Set) : nat -> Set :=
  nil  : Vec A O
| cons : forall {n} (x : A) (xs : Vec A n), Vec A (S n).

Derive Signature for Vec.
Arguments nil {_}.
Arguments cons {_} _ _.

Derive NoConfusion for Vec.

Equations noConfVec {A n} (v v' : Vec A n) : Prop :=
noConfVec nil nil := True;
noConfVec (cons _ x xs) (cons _ x' xs') :=
  {| pr1 := x; pr2 := xs |} = {| pr1 := x'; pr2 := xs' |}.
Transparent noConfVec.
Print Assumptions noConfVec_elim.

Definition noConfVec_eq {A n} (v v' : Vec A n) : v = v' -> noConfVec v v'.
Proof.
  intros ->. destruct v'; constructor.
Defined.

Definition noConfVec_eq_inv {A n} (v v' : Vec A n) : noConfVec v v' -> v = v'.
Proof.
  funelim (noConfVec v v'); try simplify *; constructor.
Defined.

Lemma noConfVec_eq_eq_inv {A n} (v v' : Vec A n) (e : v = v') :
  noConfVec_eq_inv _ _ (noConfVec_eq _ _ e) = e.
Proof.
  destruct e. destruct v; reflexivity.
Defined.

Lemma noConfVec_refl {A n} (v : Vec A n) : noConfVec v v.
Proof. destruct v; reflexivity. Defined.

Lemma noConfVec_eq_inv_eq_refl {A n} (v : Vec A n) :
  noConfVec_eq _ _ (noConfVec_eq_inv v v (noConfVec_refl v)) = (noConfVec_refl v).
Proof.
  destruct v; reflexivity.
Defined.

Lemma noConfVec_eq_inv_eq {A n} (v v' : Vec A n) (e : noConfVec v v') :
  noConfVec_eq _ _ (noConfVec_eq_inv _ _ e) = e.
Proof.
  destruct v; revert e; depelim v'; simplify *; reflexivity.
Defined.

Definition noConf_vec_equiv {A n} (v v' : Vec A n) : Equiv (v = v') (noConfVec v v').
Proof.
  refine {| equiv := noConfVec_eq v v' |}.
  unshelve refine {| equiv_inv := noConfVec_eq_inv v v' |}.
  red. intros.
  apply noConfVec_eq_inv_eq.
  red; intros.
  apply noConfVec_eq_eq_inv.
  simplify *. destruct v'; reflexivity.
Defined.

Lemma noConfVec_hom_equiv : forall {A : Set} n, NoConfusionPackage (Vec A n).
Proof.
  unshelve econstructor.
  refine noConfVec.
  apply noConfVec_eq.
  apply noConfVec_eq_inv.
  apply noConfVec_eq_eq_inv.
Defined.
Existing Instances noConfVec_hom_equiv.

Reserved Notation " x [ f ]= y " (at level 0, no associativity, f at next level, y at next level).
Inductive at_eq {A : Set} : forall{n : nat}, Vec A n -> fin n -> A -> Set :=
| here  : ∀ {n}     {x}   {xs : Vec A n}, at_eq (cons _ x xs) fin0 x
| there : ∀ {n} {i : fin n} {x y} {xs : Vec A n} (H : xs [ i ]= x),
    (cons _ y xs) [ (finS i) ]= x

where " x [ n ]= y " := (at_eq x n y).

Definition Subset := Vec bool.

Reserved Notation " x ∈ S " (at level 4).

Definition inS {n} (f : fin n) (s : Subset n) := s [ f ]= true.
Notation "x ∈ S" := (inS x S).

Equations drop_there {s n x} {p : Subset n} (H : (finS x) ∈ (cons _ s p)) : x ∈ p :=
  drop_there (there p) := p.

Inductive Dec (P : Set) : Set :=
| yes ( p :   P) : Dec P
| no ( p : P -> False) : Dec P.
Arguments yes {_} _.
Arguments no {_} _.

Equations isin {n} (x : fin n) (p : Subset n) : Dec (x ∈ p) :=
isin fin0 (cons true p) := yes here;
isin fin0 (cons false p) := no _;
isin (finS f) (cons s p) with isin f p :=
                             | yes H := yes (there H);
                             | no H := no (fun H' => _).

Next Obligation. depelim H. Defined.
Next Obligation. depelim H'. apply (H H'). Defined.
Transparent isin.
Next Obligation.
  induction x. depelim p. depelim x. constructor. constructor.
  depelim p.
  simp isin.
  constructor. apply IHx.
  destruct (isin x p). constructor. constructor.
Defined.
