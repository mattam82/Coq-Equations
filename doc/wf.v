(* begin hide *)
Require Import Equations Relation_Definitions.
Generalizable All Variables.
(* end hide *)

(** The traditional notion of well-founded relation as found in the Coq
   standard library is restricted to homogeneous relations and based on 
   the following notion of accessibility: *)

Inductive Acc {A} (R : A -> A -> Prop) (x : A) : Prop :=
| Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(** An element of [Acc A R x] contains a proof that any preceding element of 
   [x] by [R] (if any) is also accessible. As objects of [Acc] are inductive,
   there has to a finite proof for the accessibility of [x], hence all possible
   chains $\cdots R~x_{i-1} x_i, R~x_i~x$ have to be finite. This corresponds 
   (classicaly) to the descending chain condition. 
   A relation is said to be well-founded if all elements are accesible for it. 
   We make a class to register well founded relations:
*)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : forall a, Acc R a.

(** It is then trivial to derive a fixpoint combinator by recursion on 
   the accessibility proof, given a step function as before: *)

Definition FixWf `{WellFounded A R} (P : A -> Type)
  (step : Π x : A, (Π y : A, R y x -> P y) -> P x) : Π x : A, P x.
Proof. Admitted.

(** We can use the same technique as before to use this fixpoint combinator
   in [Equations] definitions. However, we need to rephrase the definitions
   in terms of inductive families to use it in general.
   An heterogeneous relation will have the form: *)

Definition hrelation {A} (T : A -> Type) :=
  forall i i', T i -> T i' -> Prop.

(** We define the accessibility predicate as a simple generalization of the
   homogeneous one where the index of the preceding term can be different from
   the one of [x]. *)

Inductive Acc_fam {A} {T : A -> Type} (R : hrelation T)
  (i : A) (x : T i) : Prop :=
  Acc_fam_intro : (Π i' (y : T i'), R i' i y x -> Acc_fam R i' y)
    -> Acc_fam R i x.

(** Again we will register well-foundedness proofs associated to a given 
   type constructor [T] as instances of: *)

Class WfFam {A} {T : A -> Type} (R : hrelation T) : Prop :=
  wf_fam : Π {i} a, Acc_fam R i a.

(** The associated fixpoint combinator is just a generalization of 
   the homogeneous one: we can just use different indices at recursive
   calls. *)

Definition FixWfFam `{WfFam A T R} (P : Π a, T a -> Type)
  (step : Π i x, (Π i' y, R i' i y x -> P i' y) -> P i x)
  (i : A) (x : T i) : P i x.
Proof. Admitted.

(** Obviously, we can prove the the generalized subterm relation defined
   earlier is well-founded. It follows by a simple induction on the object
   and inversion on the subterm proof relating the subterms and the original
   term. However, we need to take the transitive closure of this relation 
   to get the complete subterm relation. It is easy to show that the 
   transitive closure of a well-founded family relation is also well-founded: *)

(* begin hide *)
Inductive trans_clos_fam {A} {I : A -> Type} (R : hrelation I) : hrelation I :=
| trans_clos_fam_one : Π {i i'} (x : I i) (y : I i'), R _ _ x y -> trans_clos_fam R _ _ x y
| trans_clos_fam_step : Π {i i' i''} (x : I i) (y : I i') (z : I i''), 
  trans_clos_fam R _ _ x y -> R _ _ y z -> trans_clos_fam R _ _ x z.
(* end hide *)
Instance wffam_trans A (T : A -> Type) (R : hrelation T) : 
  WfFam R -> WfFam (trans_clos_fam R).
Proof. Admitted.
