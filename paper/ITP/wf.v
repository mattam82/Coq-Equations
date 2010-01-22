(** printing ~= $\simeq$ *)
(* begin hide *)
Require Import Equations Relations Transitive_Closure Bvector.
Generalizable All Variables. Set Automatic Introduction. Print clos_trans.
Derive Subterm for vector.
Check Acc. Check @Acc_intro. Definition Below : nat := 0.
(* end hide *)

(** The traditional notion of well-founded relation as found in the Coq
   standard library is restricted to homogeneous relations and based on 
   the following notion of accessibility: [[
Inductive Acc {A} (R : A -> A -> Prop) (x : A) : Prop :=
  Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x. ]]

  An element of [Acc A R x] contains a proof that any preceding element of 
  [x] by [R] (if any) is also accessible. As objects of [Acc] are inductive,
  there has to a finite proof for the accessibility of [x], hence all possible
  chains $\cdots R~x_{i-1} x_i, R~x_i~x$ have to be finite. 
  A relation is said to be well-founded if all elements of its support
  are accessible for it. This corresponds (classicaly) to the descending 
  chain condition. We make a class to register well founded relations: *)

Class WellFounded {A : Type} (R : relation A) := wellfounded : forall a, Acc R a.

(** It is then trivial to derive a fixpoint combinator by recursion on 
   the accessibility proof, given a step function as before: *)

Definition FixWf `{WF : WellFounded A R} (P : A -> Type)
  (step : Π x : A, (Π y : A, R y x -> P y) -> P x) : Π x : A, P x.
Proof. Admitted.

(** Obviously, we can prove that the direct subterm relation defined
   above is well-founded. It follows by a simple induction on the object
   and inversion on the subterm proof relating the subterms and the original
   term. We still need to take the transitive closure of this relation 
   to get the complete subterm relation. Again it is easily shown that
   transitive closure preserves well-foundedness.

   Using this recursion scheme produces more efficient
   programs, as only the needed recursive calls have to be computed along
   with the corresponding proofs of the subterm relation.
   Extraction of [FixWf] is actually a general fixpoint.
   
   We can use the same technique as before to use this fixpoint combinator
   in [Equations] definitions, we just need to deal with the currying when
   applying it to an object in an inductive family. Consider the application 
   of the fixpoint combinator for [vlast] again, our initial problem was: [[
   forall A n (v : vector A (S n)), vlast_comp A n v]]

   To apply our recursion operator over vectors, we must first prepare 
   for a dependent elimination on [v] packed with its index [n].
   To do so, we simply generalize by an equality between the packed object 
   and a fresh variable of the packed type, giving us an equivalent goal: *) 
(* begin hide *)
Definition vlast_comp A n (v : vector A (S n)) := A.
Ltac fix_wf x recname := rec_wf_eqns x recname ; unfold add_pattern ;
  destruct_exists ; simpl in *; reverse ; simplify_dep_elim ; 
    repeat curry recname ; simpl in recname.
Check projT1. Check projT2. Check nat. Check vector_subterm.
Implicit Arguments existT [ [A] [P] ].

Definition vlast A n (v : vector A (S n)) : vlast_comp A n v.

Proof.
(* end hide *)
  dependent generalize v as v'. simpl in *. revert_until v'.
  (* generalize_eqs_vars v. pack v as v'. clearbody v'. clear. intros n v0. *)
  (** [[
A : Type  v' : {index : nat & vector A index}
============================
forall n (v : vector A (S n)), v' = existT (S n) v -> vlast_comp A n v ]]
   We can now directly use the fixpoint combinator on the 
   subterm relation for packed vectors with [v']. This results in a new goal with 
   an additional induction hypothesis expecting a packed vector and 
   a proof that it is smaller than the initial packed [v]. Using currying, 
   unpacking of existentials and the dependent elimination simplification tactic,
   we get back a goal refining the initial problem with the same patterns [A n v]. *)  
  fix_wf v' rv.
  assert(forall (n' : nat) (v' : vector A (S n')),
    forall (index : nat) (y : vector A index),
       vector_subterm A (existT index y) (existT (S n) v) ->
       @existT _ (fun n => vector A n) index y = existT (S n') v' -> vlast_comp A n' v').
  intros. apply rv with index y. auto. apply H0.
  simplify_IH_hyps. simpl in X.
  (* [[
(A : Type) (n : nat) (v : vector A (S n))
recv : forall index y, vector_subterm A (existT index y) (existT (S n) v) ->
  forall n v, existT index y = existT (S n) v -> vlast_comp A n v
============================
 vlast_comp A n v ]] *)
(** 

   The last step is to provide a proof search procedure to
 automatically build proofs of the subterm relation,
 filling the witnesses that appear at recursive calls.
 We can easily do so using
 a hint database with the constructors of the $\ind{I}^{sub}$ 
 relation and lemmas on the transitive closure relation 
 that only allow to use the direct subterm relation on the right
 to guide the proof search by the refined [v], emulating the 
 unfolding strategy of [Below]. *)
  depelim v. depelim v. exact a.
  change (vlast_comp A n (Vcons a0 v)).
  apply (rv (S n) (Vcons a0 v)) ; typeclasses eauto with subterm_relation Below.
(* begin hide *)
Defined.
(* end hide *)
