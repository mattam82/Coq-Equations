Require Import Arith.
From Equations Require Import Equations.

Inductive btree (T : Type) : Type :=
   Leaf | Node (val : T) (t1 t2 : btree T).

Arguments Leaf {T}.
Arguments Node {T}.

Fixpoint count {T : Type} (p : T -> bool) (t : btree T) : nat :=
match t with
| Leaf => 0
| Node x t1 t2 =>
   (if p x then 1 else 0) + (count p t1 + count p t2)
end.

Definition size {T : Type} (t : btree T) := count (fun x => true) t.

Lemma size1 {T} (a : T) t1 t2 : size t1 < size (Node a t1 t2).
Proof.
unfold size; simpl.
unfold lt; apply Peano.le_n_S, Nat.le_add_r.
Qed.

Lemma size2 {T} (a : T) t1 t2 : size t2 < size (Node a t1 t2).
Proof.
unfold size; simpl.
unfold lt; apply Peano.le_n_S; rewrite Nat.add_comm; apply Nat.le_add_r.
Qed.

Equations redo_rev_tree {T} (t : btree T) : btree T
  by rec (size t) lt :=
   redo_rev_tree Leaf := Leaf ;
   redo_rev_tree (Node a t1 t2) := Node a (redo_rev_tree t2)
                                        (redo_rev_tree t1).

  Next Obligation.
    apply size2.
  Qed.
  Next Obligation.
    apply size1.
  Qed.

Lemma redo_rev_tree_invol {T} (t : btree T) : redo_rev_tree (redo_rev_tree t) = t.
Proof.
  funelim (redo_rev_tree t). reflexivity.
  simp redo_rev_tree. rewrite H, H0. reflexivity.
Qed.