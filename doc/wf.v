(* begin hide *)
Require Import Equations Relations Transitive_Closure Bvector.
Generalizable All Variables. Set Automatic Introduction. Print clos_trans.
Derive Subterm for vector.
Check Acc. Check @Acc_intro.
(* end hide *)

(** The traditional notion of well-founded relation as found in the Coq
   standard library is restricted to homogeneous relations and based on 
   the following notion of accessibility: [[
Inductive Acc {A} (R : A -> A -> Prop) (x : A) : Prop :=
| Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x. ]]

  An element of [Acc A R x] contains a proof that any preceding element of 
  [x] by [R] (if any) is also accessible. As objects of [Acc] are inductive,
  there has to a finite proof for the accessibility of [x], hence all possible
  chains $\cdots R~x_{i-1} x_i, R~x_i~x$ have to be finite. This corresponds 
  (classicaly) to the descending chain condition. 
  A relation is said to be well-founded if all elements are accessible for it. 
   We make a class to register well founded relations: *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : forall a, Acc R a.

(** It is then trivial to derive a fixpoint combinator by recursion on 
   the accessibility proof, given a step function as before: *)

Definition FixWf `{WF : WellFounded A R} (P : A -> Type)
  (step : Π x : A, (Π y : A, R y x -> P y) -> P x) : Π x : A, P x.
Proof. Admitted.

(** Obviously, we can prove that the subterm relation defined
   above is well-founded. It follows by a simple induction on the object
   and inversion on the subterm proof relating the subterms and the original
   term. However, we need to take the transitive closure of this relation 
   to get the complete subterm relation. It is easy to show that the 
   transitive closure of a well-founded relation is also well-founded.

   We can use the same technique as before to use this fixpoint combinator
   in [Equations] definitions. However, we need to take care that before 
   applying the fixpoint combinator to an object in an inductive family,
   we must first package it in a dependent sum. Consider the following 
   programming problem: *)

Definition vlast_comp A n (v : vector A (S n)) := A.

(* begin hide *)
Ltac fix_wf x recname := rec_wf_eqns x recname ; unfold add_pattern ;
  destruct_exists ; simpl in *; reverse ; simplify_dep_elim ; 
    repeat curry recname ; simpl in recname.
Check projT1. Check projT2. Check nat. Check vector_subterm.
Implicit Arguments existT [ [A] [P] ].
(* end hide *)

Definition vlast A n v : vlast_comp A n v.
Proof.
  (** If we want to apply our recursion operator over vectors here, 
     we must first pack [v] with it's index [n]. 
     We have a tactic [pack v as vpack] that will take [v] and 
     produce a dependent tuple packaging it with its indices.
     As all the indices are variables (at least after dependent
     generalization), we can replace any occurrence of the indices 
     or the term by the corresponding projections of the tuple. *)
  generalize_eqs_vars v. pack v as v'.
  (** [[
(A : Type) (gen_x : nat) (v : vector A gen_x)
v' := existT gen_x v : {index : nat & vector A index}
============================
 forall (n : nat) (v0 : vector A (S n)),
 projT1 v' = S n -> projT2 v' ~= v0 -> vlast_comp A n v0 ]]
   Without loss of generality we can then clear the body of the 
   packed object and all the variables we packed. *)
  clearbody v'. clear.
  (** [[
(A : Type) (v' : {index : nat & vector A index})
============================
 forall (n : nat) (v0 : vector A (S n)),
 projT1 v' = S n -> projT2 v' ~= v0 -> vlast_comp A n v0 ]]
   We can now directly use the fixpoint combinator on the 
   (uncurried) subterm relation for vectors, which expects
   a predicate on the packed type. This is done by the tactic
   [fix_wf x n] that takes the variable we want to recurse on
   and the name of the recursive functional and applies the 
   recursor associated to the type of [x]. *)  
  fix_wf v' rv.
  (** [[
(A : Type) (n : nat) (v0 : vector A (S n))
rv : forall (index : nat) (y : vector A index),
  vector_subterm A (existT index y) (existT (S n) v0) ->
  forall (n : nat) (v0 : vector A (S n)),
  index = S n -> y ~= v0 -> vlast_comp A n v0
============================
 vlast_comp A n v0 ]]
 The tactic also simplifies the goal by unpacking the existentials 
 for the initial argument and currying the functional back.
 Now we can decompose the vector and do our recursive call.
 The last step is to provide a proof search procedure to 
 automatically build proofs of the subterm relation,
 filling the witnesses that appear at recursive calls (i.e. the 
 [vector_subterm] hypothesis here). We can easily do so using
 a hint database with the constructors of the $\ind{I}^{sub}$ 
 relation and the constructors for the transitive closure relation.
 
 We can turn this whole process into a single tactic called at
 recursion nodes. *)
  depelim v0. depelim v0. exact a.
  change (vlast_comp A n (Vcons a0 v0)).
  apply (rv (S n) (Vcons a0 v0)) ; typeclasses eauto with subterm_relation Below.
Defined.
