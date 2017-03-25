(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Equations Fin DepElimDec.
Require Import Omega.

Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations(nocomp) list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).

  Context {B : Type}.
  Equations(nocomp) list_map_size (l : list A)
           (g : forall (x : A), f x < list_size l -> B) : list B :=
  list_map_size nil _ := nil;
  list_map_size (cons x xs) g := cons (g x _) (list_map_size xs (fun x H => g x _)).
  Next Obligation.
    simp list_size. auto with arith.
  Defined.    
  Next Obligation.
    simp list_size. omega.
  Defined.    

  Lemma list_map_size_spec (g : A -> B) (l : list A) :
    list_map_size l (fun x _ => g x) = List.map g l.
  Proof.
    funelim (list_map_size l (λ (x : A) (_ : f x < list_size l), g x)); simpl; trivial.
    now rewrite H.
  Qed.
End list_size.

Require Import List.

Module RoseTree.

  Section roserec.
    Context {A : Set} {A_eqdec : EqDec.EqDec A}.
    
    Inductive t : Set :=
    | leaf (a : A) : t
    | node (l : list t) : t.
    Derive NoConfusion for t.
    
    Fixpoint size (r : t) :=
      match r with
      | leaf a => 0
      | node l => S (list_size size l)
      end.

    Section elimtree.
      Context (P : t -> Type) (Pleaf : forall a, P (leaf a))
              (Pnil : P (node nil))
              (Pnode : forall x xs, P x -> P (node xs) -> P (node (cons x xs))).
              
      Equations(nocomp noind) elim (r : t) : P r :=
      elim r by rec r (MR lt size) :=
      elim (leaf a) := Pleaf a;
      elim (node nil) := Pnil;
      elim (node (cons x xs)) := Pnode x xs (elim x) (elim (node xs)).

      Next Obligation.
        red. simpl. omega.
      Defined.
      Next Obligation.
        red. simpl. omega.
      Defined.
    End elimtree.

    Equations(nocomp) elements (r : t) : list A :=
    elements l by rec r (MR lt size) :=
    elements (leaf a) := [a];
    elements (node l) := concat (list_map_size size l (fun x H => elements x)).
    
    Next Obligation.
      intros. simpl in *. red. simpl. omega.
    Defined.
      
    Equations(nocomp) elements_def (r : t) : list A :=
    elements_def (leaf a) := [a];
    elements_def (node l) := concat (List.map elements l).
    Lemma elements_equation (r : t) : elements r = elements_def r.
    Proof.
      funelim (elements r); simp elements_def.
      now rewrite list_map_size_spec.
    Qed.

    (** To solve measure subgoals *)
    Hint Extern 4 (_ < _) => abstract (simpl; omega) : rec_decision.
    Hint Extern 4 (MR lt _ _ _) => abstract (red; simpl in *; omega) : rec_decision.

(* Nested rec *) 
    Equations(nocomp) elements' (r : t) : list A :=
    elements' l by rec r (MR lt size) :=
    elements' (leaf a) := [a];
    elements' (node l) := fn l _

    where fn (x : list t) (H : list_size size x < size (node l)) : list A :=
    fn x H by rec x (MR lt (list_size size)) :=
    fn nil _ := nil;
    fn (cons x xs) _ := elements' x ++ fn xs _.

    Next Obligation.
      abstract (simpl; omega).
    Defined.

    Equations(nocomp) elements'_def (r : t) : list A :=
    elements'_def (leaf a) := [a];
    elements'_def (node l) := concat (List.map elements' l).

    Lemma elements'_equation (r : t) : elements' r = elements'_def r.
    Proof.
      pose (fun_elim (f:=elements')).
      apply (p (fun r f => f = elements'_def r) (fun l x H r => r = concat (List.map elements' x))); clear p;
        simp elements'_def.

      intros. simpl. f_equal.
      (** Needs missing IH on nested recursive call *)
      admit.
    Admitted.


  End roserec.
  Arguments t : clear implicits.

  Section fns.
    Context {A B : Set} (f : A -> B) (g : B -> A -> B) (h : A -> B -> B).
    
    Equations(nocomp) map (r : t A) : t B :=
    map (leaf a) := leaf (f a);
    map (node l) := node (List.map map l).

    Equations(nocomp) fold (acc : B) (r : t A) : B :=
    fold acc (leaf a) := g acc a;
    fold acc (node l) := List.fold_left fold l acc.

    Equations(nocomp) fold_right (r : t A) (acc : B) : B :=
    fold_right (leaf a) acc := h a acc;
    fold_right (node l) acc := List.fold_right fold_right acc l.
  End fns.    

End RoseTree.
