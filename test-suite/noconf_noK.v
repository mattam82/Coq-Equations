From Equations Require Import Equations DepElimDec HSets.
(* Set Universe Polymorphism. *)
(** Can we define NoConfusion in SProp (squashing equalities of arguments)?
    Would not allow to show equivalence to (x = y) for non-strict sets. *)


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
(* | cons' : forall {n} (x : A), Vec E A (S n) *)
(* | cons3 : forall n, Vec E A n. *)

Derive Signature for Vec.
Arguments nil {_ _}.
Arguments cons {_ _ _} _ _.
(* Arguments cons' {_ _ _} _ . *)


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

(* Equations noConfVec {E A n} (v v' : Vec E A n) : Prop := *)
(* noConfVec nil nil := True; *)
(* noConfVec (cons _ x xs) (cons _ x' xs') := *)
(*   {| pr1 := x; pr2 := xs |} = {| pr1 := x'; pr2 := xs' |}; *)
(* noConfVec (cons' x) (cons' x') := x = x'; *)
(* noConfVec cons3 cons3 := True; *)
(* noConfVec _ _ := False. *)
(* Transparent noConfVec. *)
(* Print Assumptions noConfVec_elim. *)

(* Next Obligation. *)
(* Proof. *)
(*   depelim v. *)
(*   generalize_eqs_sig v'. destruct v'. *)
(*   simplify ?. *)
(*   refine (eq_simplification_sigma1_dep _ _ _ _ _). destruct v'; *)
(*   simplify *. constructor. *)
(*   generalize_eqs_sig v'. *)
(*   refine (eq_simplification_sigma1_dep _ _ _ _ _). destruct v'; *)
(*   simplify *; constructor. *)
(*   generalize_eqs_sig v'. *)
(*   refine (eq_simplification_sigma1_dep _ _ _ _ _). destruct v'; *)
(*                                                      simplify *; constructor. *)
(* Defined. *)

(* Definition noConfVec_eq {E A n} (v v' : Vec E A n) : v = v' -> noConfVec v v'. *)
(* Proof. *)
(*   intros ->. destruct v'; constructor. *)
(* Defined. *)

(* Definition noConfVec_eq_inv {E A n} (v v' : Vec E A n) : noConfVec v v' -> v = v'. *)
(* Proof. *)
(*   funelim (noConfVec v v'); try simplify *; constructor. *)
(*   (* refine (@f_equal _ _ (fun x => cons x.1 x.2) _ _). *) *)
(*   (* simplify ?. *) *)
(*   (* simplify ?. *) *)
(*   (* refine (@f_equal _ _ (fun x => cons' x) _ _). *) *)
(* Defined. *)

(* Lemma noConfVec_eq_eq_inv {E A n} (v v' : Vec E A n) (e : v = v') : *)
(*   noConfVec_eq_inv _ _ (noConfVec_eq _ _ e) = e. *)
(* Proof. *)
(*   destruct e. destruct v; reflexivity. *)
(* Defined. *)

(* Lemma noConfVec_refl {E A n} (v : Vec E A n) : noConfVec v v. *)
(* Proof. destruct v; reflexivity. Defined. *)

(* Lemma noConfVec_eq_inv_eq_refl {E A n} (v : Vec E A n) : *)
(*   noConfVec_eq _ _ (noConfVec_eq_inv v v (noConfVec_refl v)) = (noConfVec_refl v). *)
(* Proof. *)
(*   destruct v; reflexivity. *)
(* Defined. *)

(* Lemma noConfVec_eq_inv_eq {E A n} (v v' : Vec E A n) (e : noConfVec v v') : *)
(*   noConfVec_eq _ _ (noConfVec_eq_inv _ _ e) = e. *)
(* Proof. *)
(*   destruct v; revert e; depelim v'; simplify *; reflexivity. *)
(* Defined. *)

Definition NoConfVec {E A n} (v v' : Vec E A n) : Prop :=
  match v in Vec _ _ n return Vec E A n -> Prop with
  | nil => fun v' =>
             match v' in Vec _ _ O return Prop with
             | nil => True
             end
  | @cons _ _ n' x xs =>
    fun v' =>
      match v' in Vec _ _ (S n'') return Vec E A n'' -> Prop with
      | @cons _ _ n'' x' xs' => fun xs => {| pr1 := x; pr2 := xs |} = {| pr1 := x'; pr2 := xs' |}
      end xs
  end v'.

(* Definition noConfVec_eq {E A n} (v v' : Vec E A n) : v = v' -> NoConfVec v v'. *)
(* Proof. *)
(*   intros ->. destruct v'. constructor. simpl. constructor. simpl. constructor. *)
(* Defined. *)

(* Definition idx0_elim {E A} (P : Vec E A O -> Type) (H : P nil) : forall v, P v := *)
(*   fun v => match v in Vec _ _ O return P v with *)
(*            | nil => H *)
(*            end. *)

(* Definition idxS_elim {E A} (P : forall n, Vec E A (S n) -> Type) *)
(*            (H : forall n a (v' : Vec E A n), P n (cons a v')) *)
(*            (H' : forall n a, P n (cons' a)) *)
(*            n v : P n v := *)
(*   match v in Vec _ _ (S n') with *)
(*   | cons a v' => H _ a v' *)
(*   | cons' a => H' _ a *)
(*   end. *)

(* (* refine (match v as v' in Vec _ _ n' return *) *)
(* (*                 match n' as n'' return Vec E A n'' -> Type with *) *)
(* (*                 | O => fun _ => True *) *)
(* (*                 | S n' => fun v => P _ v *) *)
(* (*                 | raise _ _ => fun _ => True *) *)
(* (*                 end v' *) *)
(* (*           with *) *)
(* (*           | nil => I *) *)
(* (*           | cons a v' => H _ a v' *) *)
(* (*           | cons' a => H' _ a *) *)
(* (*           end). *) *)

(* Definition isNil {E A n} (v : Vec E A n) := *)
(*   match v with *)
(*   | nil => True *)
(*   | _ => False *)
(*   end. *)

(* Lemma eq_simplification_sigma1_dep@{i j} {A : Type@{i}} {P : A -> Type@{i}} {B : Type@{j}} *)
(*   (p q : A) (x : P p) (y : P q) : *)
(*   (forall e : p = q, (@eq_rect A p P x q e) = y -> B) -> *)
(*   (sigmaI P p x = sigmaI P q y -> B). *)
(* Proof. *)
(*   intros. revert X. *)
(*   change p with (pr1 &(p& x)). *)
(*   change q with (pr1 &(q & y)). *)
(*   change x with (pr2 &(p& x)) at 3. *)
(*   change y with (pr2 &(q & y)) at 4. *)
(*   destruct H. *)
(*   intros X. eapply (X eq_refl). apply eq_refl. *)
(* Defined. *)

(* (* Definition isNil_eq {E A } (v : Vec E A O) : isNil v -> v = nil. *) *)
(* (* Proof. destruct v. *) *)
(* (*   match v with *) *)
(* (*   | nil => True *) *)
(* (*   | _ => False *) *)
(* (*   end. *) *)
(* Set Printing Universes. *)
(* Definition noConfVec_eq_inv {E A n} (v v' : Vec E A n) : NoConfVec v v' -> v = v'. *)
(* Proof. *)
(*   destruct v. *)
(*   generalize_eqs_sig v'. *)
(*   refine (eq_simplification_sigma1_dep _ _ _ _ _). destruct v'. *)
(*   simplify ?. simplify ?. simplify ?. simpl. reflexivity. *)
(*   simplify ?. *)
(*   simplify ?. *)
(*   simpl. simplify ?. simplify ?. *)
(*   intros. *)
(*   generalize_eqs_sig v'. destruct v'. *)
(*   simplify ?. *)
(*   simplify ?. *)
(*   simpl in H. apply (f_equal (fun x => cons x.1 x.2)) in H. apply H. *)
(*   simplify ?. simpl in H. *)
(*   elim H. *)
(*   generalize_eqs_sig v'. destruct v'. *)
(*   simplify *. *)
(*   simplify *. *)
(*   simplify *. reflexivity. *)
(*   (* revert v'. refine (idx0_elim _ _). intros. constructor. *) *)
(*   (* revert n v' v. refine (idxS_elim _ _ _). *) *)
(*   (* simpl. intros. change a with (&(a & v').1). change v' with (&(a & v').2) at 2. *) *)
(*   (* destruct H. reflexivity. simpl. intros. elim H. *) *)
(*   (* revert n v'. refine (idxS_elim _ _ _). simpl. intros. elim H. *) *)
(*   (* simpl. intros n a H. destruct H; reflexivity. *) *)
(* Defined. *)

(* Lemma noConfVec_eq_eq_inv {E A n} (v v' : Vec E A n) (e : v = v') : *)
(*   noConfVec_eq_inv _ _ (noConfVec_eq _ _ e) = e. *)
(* Proof. *)
(*   destruct e. destruct v; reflexivity. *)
(* Defined. *)

(* Lemma noConfVec_refl {E A n} (v : Vec E A n) : NoConfVec v v. *)
(* Proof. destruct v; reflexivity. Defined. *)

(* Lemma noConfVec_eq_inv_eq_refl {E A n} (v : Vec E A n) : *)
(*   noConfVec_eq _ _ (noConfVec_eq_inv v v (noConfVec_refl v)) = (noConfVec_refl v). *)
(* Proof. *)
(*   destruct v; reflexivity. *)
(* Defined. *)

(* Lemma noConfVec_eq_inv_eq {E A n} (v v' : Vec E A n) (e : NoConfVec v v') : *)
(*   noConfVec_eq _ _ (noConfVec_eq_inv _ _ e) = e. *)
(* Proof. *)
(*   destruct v. revert e. *)
(*   generalize_eqs_vars_sig v'. destruct v'. intros v'. *)
(*   refine (eq_simplification_sigma1_dep _ _ _ _ _). simplify ?. *)
(*   simplify ?. simplify ?. simplify ?. reflexivity. *)
(*   intro. simplify *. *)
(*   intro. simplify *. *)

(*   depelim v'. simpl in e. *)
(*   revert e. simplify *. simpl. reflexivity. *)
(*   simpl. intros. elim e. *)
(*   depelim v'. simpl in e. *)
(*   revert e. simplify *. *)
(*   revert e. simplify *. reflexivity. *)
(* Defined. *)

(* (*   destruct v. revert v' e. refine (idx0_elim _ _). simpl. destruct e. reflexivity. *) *)
(* (*   revert n v' v e. refine (idxS_elim _ _ _). intros. *) *)
(* (*   simpl in e. *) *)
(* (*   revert e. simplify *. simpl. reflexivity. *) *)
(* (*   simpl. intros. elim e. *) *)
(* (*   revert n v' e. refine (idxS_elim _ _ _). intros. elim e. *) *)
(* (*   intros ??. simplify *. simpl. reflexivity. *) *)
(* (* Defined. *) *)

Definition noConf_vec_equiv {E A n} (v v' : Vec E A n) : Equiv (v = v') (noConfVec v v').
Proof.
  refine {| equiv := noConfVec_eq v v' |}.
  unshelve refine {| equiv_inv := noConfVec_eq_inv v v' |}.
  red. intros.
  apply noConfVec_eq_inv_eq.
  red; intros.
  apply noConfVec_eq_eq_inv.
  simplify *. destruct v'; reflexivity.
Defined.

Lemma noConfVec_hom_equiv : forall {E A : Set} n, NoConfusionPackage (Vec E A n).
Proof.
  unshelve econstructor.
  refine noConfVec.
  apply noConfVec_eq.
  apply noConfVec_eq_inv.
  apply noConfVec_eq_eq_inv.
Defined.
Existing Instances noConfVec_hom_equiv.

Equations param_vector_vcons E (A : Set) (a : A) (n : ℕ E) (v : Vec E A n)
          (X : vector_param E A (S n) (cons a v)) : vector_param E A n v :=
  param_vector_vcons E A _ _ _  (vcons_param _ _ _ X) := X.
Transparent param_vector_vcons.
