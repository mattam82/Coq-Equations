(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Program.
From Equations Require Import Equations Fin.
Require Import Omega Utf8.

Require Import List.

Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
  map_In nil _ := nil;
  map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = List.map f l.
Proof.
  remember (fun (x : A) (_ : In x l) => f x) as g.
  funelim (map_In l g); rewrite ?H; trivial.
Qed.
  
Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).
  
  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size xs).
  Proof.
    intros. funelim (list_size xs); simpl in *. destruct H.
    destruct H0.
    * subst; omega.
    * specialize (H _ H0). intuition.
  Qed.
End list_size.

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
              
      Equations(noind) elim (r : t) : P r by rec (size r) lt :=
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

    Equations elements (r : t) : list A by rec (size r) lt :=
    elements (leaf a) := [a];
    elements (node l) := concat (map_In l (fun x H => elements x)).
    
    Next Obligation.
      intros. simpl in *. red. simpl.
      apply In_list_size. auto.
    Defined.
      
    Equations elements_def (r : t) : list A :=
    elements_def (leaf a) := [a];
    elements_def (node l) := concat (List.map elements l).
    Lemma elements_equation (r : t) : elements r = elements_def r.
    Proof.
      funelim (elements r); simp elements_def.
      now rewrite map_In_spec.
    Qed.

    (** To solve measure subgoals *)
    Hint Extern 4 (_ < _) => abstract (simpl; omega) : rec_decision.
    Hint Extern 4 (MR _ _ _ _) => abstract (repeat red; simpl in *; omega) : rec_decision.

    (* Nested rec *) 
    Set Equations Debug.

    Ltac Equations.Subterm.rec_wf_eqns_rel recname x rel ::=
      Subterm.rec_wf_rel_aux recname x rel ltac:(fun rechyp => add_pattern (hide_pattern rechyp));
      unfold MR in *; simpl in *; try match goal with
      | [ H : unit |- _ ] => destruct H
      end.

    Goal forall (l : list t) (elements' : (∀ r : t, MR lt size r (node l) → list A))
                (x : list t) (H : list_size size x < size (node l)), True.
      set_eos.
      intros.
      assert (eos' := the_end_of_the_section). move eos' before elements'.
      Subterm.rec_wf_eqns_rel fn x (MR lt (list_size size)).
    Admitted.

    Equations(noind) elements' (r : t) : list A by rec r (MR lt size) :=
    elements' (leaf a) := [a];
    elements' (node l) := fn l hidebody

    where fn (x : list t) (H : list_size size x < size (node l)) : list A by rec x (MR lt (list_size size)) :=
    fn nil _ := nil;
    fn (cons x xs) _ := elements' x ++ fn l elements' xs hidebody.

    Next Obligation.
      abstract (simpl; omega).
    Defined.

    Next Obligation.
      abstract (red; simpl; omega).
    Defined.

    Equations elements'_def (r : t) : list A :=
    elements'_def (leaf a) := [a];
    elements'_def (node l) := concat (List.map elements' l).

    Lemma elements'_equation (r : t) : elements' r = elements'_def r.
    Proof.
      pose (fun_elim (f:=elements')).
      apply (p (fun r f => f = elements'_def r) (fun l x H r => r = concat (List.map elements' x)));
        clear p; intros; simp elements'_def.
      simpl. f_equal. apply H2.
    Qed.
    
  End roserec.
  Arguments t : clear implicits.

  Section fns.
    Context {A B : Set} (f : A -> B) (g : B -> A -> B) (h : A -> B -> B).
    
    Equations map (r : t A) : t B :=
    map (leaf a) := leaf (f a);
    map (node l) := node (List.map map l).

    Equations fold (acc : B) (r : t A) : B :=
    fold acc (leaf a) := g acc a;
    fold acc (node l) := List.fold_left fold l acc.

    Equations fold_right (r : t A) (acc : B) : B :=
    fold_right (leaf a) acc := h a acc;
    fold_right (node l) acc := List.fold_right fold_right acc l.
  End fns.    

End RoseTree.
