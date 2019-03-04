Require Import HoTT.Basics.Overture.

Local Open Scope list_scope.

Module HoTTUtil.
  Local Set Implicit Arguments.
  Local Set Maximal Implicit Insertion.

  Definition tl A (x : list A) : list A :=
    match x with
    | nil => nil
    | _ :: t => t
    end.

  Definition hd A (x : list A) : option A :=
    match x with
    | nil => None
    | h :: _ => Some h
    end.

  Lemma nat_path_to_S (n m : nat) (H : n = m) : n.+1 = m.+1.
  Proof. rewrite H; reflexivity. Defined.

  Lemma nat_path_from_S (n m : nat) (H : n.+1 = m.+1) : n = m.
  Proof. refine (
    match H in _ = i return
      match i with
      | 0 => n = m
      | S i => n = i
      end
    with
    | idpath => idpath
    end
  ). Defined.

  Lemma nat_path_O_S (n : nat) (H : O = n.+1) : Empty.
  Proof. refine (
    match H in _ = i return
      match i with
      | O => Unit
      | _.+1 => Empty
      end
    with
    | idpath => tt
    end
  ). Defined.

  Lemma nat_path_S_O (n : nat) (H : n.+1 = O) : Empty.
  Proof. eapply nat_path_O_S. exact (symmetry _ _ H). Defined.

End HoTTUtil.

Import HoTTUtil.
Create HintDb nat_paths.
Hint Resolve nat_path_to_S nat_path_from_S nat_path_O_S nat_path_S_O : nat_paths.
