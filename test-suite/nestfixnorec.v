From Equations Require Import Equations.
Set Keyed Unification.

Require Import Coq.Lists.List.
Import ListNotations.

Inductive tree a := Node : a -> list (tree a) -> tree a.

Equations elements {a} (t : tree a) : list a := {
  elements (Node x ts) => x :: list_elements ts }

where list_elements {a} (l : list (tree a)) : list a :=
  { list_elements nil := nil;
    list_elements (cons a l) := elements a ++ list_elements l }.

Lemma list_elements_spec {A} (l : list (tree A)) : list_elements l = List.concat (List.map elements l).
Proof.
  induction l; simp elements; trivial. rewrite IHl. simpl. auto.
Qed.
#[local] Hint Rewrite @list_elements_spec : elements.

Class C a := {  P : a -> bool }.

(* Arguments P {_}. *)

Definition list_P {a} (a_C : C a) : list a -> bool := existsb P.

Definition list_C  {a} (a_C : C a) : C (list a) := {| P := list_P a_C |}.

(* Note that *)
(* Eval cbn in       fun a C => (P (list_C C)). *)
(* evaluates to:  fun a C  => list_P C *)



(* (* Works, using a local record *) *)
(* Fixpoint tree_P1 {a} (a_C : C a) (t : tree a) : bool := *)
(*     let tree_C := Build_C _ (tree_P1 a_C) in *)
(*     let list_C' := Build_C _ (list_P tree_C) in *)
(*     match t with Node _ x ts => orb (P a_C x) (P list_C' ts) end. *)

(* Definition tree_C  {a} {a_C : C a} : C (tree a) := {| P := tree_P1 a_C |}. *)

(* Works too, using list_P directly *)
Fixpoint tree_P2 {a} (a_C : C a) (t : tree a) : bool :=
    let tree_C := Build_C _ (tree_P2 a_C) in
    match t with Node _ x ts => orb (P x) (list_P tree_C ts) end.

(* Does not work, using a globally defined record. Why not? *)

(* Eval compute in (fun f => P (list_C f)). *)

Fixpoint tree_P3 {a} (a_C : C a) (t : tree a) : bool :=
    let tree_C := Build_C _ (tree_P3 a_C) in
    match t with Node _ x ts => orb (P x) (P (C:=list_C tree_C) ts) end.

Module Works.

Section tree_list.

  Context {a} (a_C : C a).

  Equations tree_P3 (t : tree a) : bool := {
  tree_P3 (Node x ts) => orb (P x) (list_P3 ts) }

  where list_P3 (l : list (tree a)) : bool := {
   list_P3 nil := false;
   list_P3 (cons l ls) := tree_P3 l || list_P3 ls }.

  Global Instance tree_C : C (tree a) := { P := tree_P3 }.
  Global Instance tree_list_C : C (list (tree a)) := { P := list_P3 }.

End tree_list.

Example check := (fun a (a_C : C a) => eq_refl : tree_list_C a_C = list_C (tree_C a_C)).

End Works.

Module Ideal.

Section tree_list.

  Context {a} (a_C : C a).

  Equations tree_P3 (t : tree a) : bool := {
  tree_P3 (Node x ts) => orb (P x) (list_P3 ts) }

  where list_P3 (l : list (tree a)) : bool := {
  list_P3 l := existsb tree_P3 l }.

  Global Instance tree_C : C (tree a) := { P := tree_P3 }.
  Global Instance tree_list_C : C (list (tree a)) := { P := list_P3 }.

End tree_list.

Example check := (fun a (a_C : C a) => eq_refl : tree_list_C a_C = list_C (tree_C a_C)).



End Ideal.

Set Equations Transparent.

Equations myexistsb {A} (P : A -> bool) (l : list A) : bool :=
myexistsb P nil := false;
myexistsb P (cons x xl) := orb (P x) (myexistsb P xl).

Equations myexistsb_prop {A} (P : A -> Prop) (l : list A) : Prop :=
myexistsb_prop P nil := False;
myexistsb_prop P (cons x xl) := P x \/ (myexistsb_prop P xl).

Inductive reflect (P : Prop) : bool -> Prop :=
| reflectT : P -> reflect P true
| reflectnT : ~ P -> reflect P false.

Inductive myexists_graph {A} (p : A -> bool) (P : A -> Prop) (R : forall x, reflect (P x) (p x))
  : forall (l : list A), bool -> Prop :=
  myexists_graph_1 : myexists_graph p P R [] false
| myexists_graph_2 t l b : P t -> myexists_graph p P R l b -> myexists_graph p P R [] (p t || existsb p l).
Lemma myexistsb_prop_exits {A} (P : A -> Prop) (l : list A) : myexistsb_prop P l <-> Exists P l.
Proof.
  funelim (myexistsb_prop P l). split; intuition auto. inversion H.
  rewrite H. split; intuition auto. inversion H0. intuition.
  subst. intuition auto.
Qed.

Section RoseTreeInd.
  Context {A : Type}.
  Context {P : tree A -> Type}.
  Context {P0 : list (tree A) -> Type}.
  Context (f : forall (a : A) (t : list (tree A)),
              P0 t -> P (Node _ a t)).
  Context (fnil : P0 nil).
  Context (fcons : forall a t, P a -> P0 t -> P0 (cons a t)).

  Equations tree_elim (t : tree A) : P t := {
  tree_elim (Node x ts) := f x ts (list_tree_elim ts) }

  where list_tree_elim (l : list (tree A)) : P0 l := {
  list_tree_elim nil := fnil;
  list_tree_elim (cons a t) := fcons a t (tree_elim a) (list_tree_elim t) }.
End RoseTreeInd.

Require Import Bool.

Module IdealNoSec.

  Equations tree_P3 {a} {a_C : C a} (t : tree a) : bool := {
  tree_P3 (Node x ts) => orb (P x) (list_P3 ts) }

  where list_P3 {a} {a_C : C a} (l : list (tree a)) : bool := {
  list_P3 l := existsb tree_P3 l }.

  #[export]
  Instance tree_C {a} (a_C : C a) : C (tree a) := { P := tree_P3 }.
  #[export]
  Instance tree_list_C {a} (a_C : C a) : C (list (tree a)) := { P := list_P3 }.

  Example check0 := (fun a (a_C : C a) => eq_refl : tree_list_C a_C = list_C (tree_C a_C)).

  Set Firstorder Solver auto.

  (* It is impossible to derive the good nested elimination principle from the
   o ne generated automatically, one has to redo the nested fixpoint construction *)
  Definition my_P3_elim :
    forall (P0 : forall a : Type, C a -> tree a -> bool -> Prop)
           (P1 : forall a, C a -> list (tree a) -> bool -> Prop),
      (forall (a : Type) (a_C : C a) (a0 : a) (l : list (tree a)),
          P1 a a_C l (list_P3 l) -> P0 a a_C (Node a a0 l) (P a0 || list_P3 l)%bool) ->
      (forall (a : Type) (a_C : C a), P1 a a_C [] false) ->
      (forall (a : Type) (a_C : C a) t l, P0 a a_C t (tree_P3 t) ->
                                          P1 a a_C l (list_P3 l) ->
                                          P1 a a_C (t :: l) (existsb (tree_P3 ) (t :: l))) ->
          (forall (a : Type) (a_C : C a) (t : tree a), P0 a a_C t (tree_P3 t))  /\
      (forall (a : Type) (a_C : C a) (l : list (tree a)), P1 a a_C l (list_P3 l)).
  Proof.
    intros.
    assert((forall (a : Type) (a_C : C a) (t : tree a), P0 a a_C t (tree_P3 t))).
    fix my_P3_elim 3. destruct t. simpl. apply H.
    revert l. fix my_P3_elim0 1. destruct l; simpl. apply H0. apply H1. apply my_P3_elim.
    apply my_P3_elim0.
    firstorder.
    revert l. fix my_P3_elim 1. destruct l; simpl. apply H0. apply H1. apply H2. apply my_P3_elim.
  Defined.

  Section P3_proof.
    Context {a} {a_C : C a}.
    #[local] Hint Rewrite in_app_iff : In.
    Lemma P3_test (t : tree a) : tree_P3 t = true ->
                                 exists x, In x (elements t) /\ P x = true.
    Proof.
      revert t.
      refine (tree_elim (P0:=fun t : list (tree a) => list_P3 t = true ->
                                                      exists x : a, In x (list_elements t) /\ P x = true) _ _ _); clear; intros.
      simp tree_P3 in H0.
      rename H0 into Hal.
      - rewrite orb_true_iff in Hal. destruct Hal as [Hal|Hal].
        + exists a0. simp elements. intuition auto with datatypes.
        + simp tree_P3 in H.
          specialize (H Hal).
          simp elements.
          destruct H as (ex & exl & Pexl).
          simp elements in *.
          exists ex.
          simpl.
          intuition auto.

      - simpl in H. discriminate.
      - simpl in H1. rewrite orb_true_iff in H1.
        destruct H1. specialize (H H1).
        firstorder.
        exists x. simpl. rewrite in_app_iff. firstorder.

        specialize (H0 H1).
        simpl. destruct H0. exists x. rewrite in_app_iff; firstorder.
    Qed.

    Lemma P3_test2 (t : tree a) : tree_P3 t = true ->
                                 exists x, In x (elements t) /\ P x = true.
    Proof.
      revert a a_C t.
      refine (proj1 (my_P3_elim
                       (fun a a_C t b => b = true -> exists x : a, In x (elements t) /\ P x = true)
                       (fun a aC (t : list (tree a)) b =>
                          b = true ->
                          exists x : a, In x (list_elements t) /\ P x = true) _ _ _)); clear; intros.
      rename H0 into Hal.
      - rewrite orb_true_iff in Hal. destruct Hal as [Hal|Hal].
        + exists a0. simp elements. intuition auto with datatypes.
        + specialize (H Hal).
          simp elements.
          destruct H as (ex & exl & Pexl).
          simp elements in *.
          exists ex.
          simpl.
          intuition auto.

      - discriminate.
      - simpl in H1. rewrite orb_true_iff in H1.
        destruct H1. specialize (H H1).
        firstorder.
        exists x. simpl. rewrite in_app_iff. firstorder.

        specialize (H0 H1).
        simpl. destruct H0. exists x. rewrite in_app_iff; firstorder.
    Qed.
  End P3_proof.
End IdealNoSec.
