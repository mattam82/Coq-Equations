(** * Working with vectors

  We quickly develop a proof that vector reversal is involutive
  for indexed vectors. We also show the equivalence of the tail recursive 
  and naïve versions of vector reversal.

  To avoid transport hell, we reason on the total space [Σ n : nat, vector A n]
  and use (dependent) equational reasoning. This requires a few support definitions
  to move between transport equalities and total space equalities and to show 
  appropriately generalized congruence lemmas on the definitions, but once this setup
  is done, the proofs ressemble the usual reasoning on lists. *)

From Stdlib Require Import Arith ssreflect.
From Equations Require Import Equations.

Set Equations Transparent.

Section vectors.
  Variable T : Type.
  Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall {n}, T -> vector n -> vector (S n).

  (** Let's define some more notation *)
  Local Notation "[]" := Vnil.
  Local Notation "x :: y" := (@Vcons _ x y).

  Declare Scope vec_scope.
  Delimit Scope vec_scope with vec.
  Bind Scope vec_scope with vector.
  Open Scope vec_scope.

  Reserved Notation "x ++ y" (right associativity, at level 60).

  (* Usual concatenation *)
  Equations app {n m : nat} (v1 : vector n) (v2 : vector m) : vector (n + m) :=
  { [] ++ v2 := v2 ;
    (x :: xs) ++ v2 := x :: xs ++ v2 }
  where "x ++ y" := (app x y) : vec_scope.

  (* This uses (_, _) to denote the sigma type pairing. *)
  Import Sigma_Notations.

  Import EqNotations.

  (** Essential simplification lemmas when working in the "total" space [Σ n, vector n] *)
  (* This uses (provable) UIP *)
  Set Equations With UIP.

  Lemma eq_cons {n m} (v : vector n) (v' : vector m) x : (n, v) = (m, v') -> (S n, x :: v) = (S m, x :: v').
  Proof.
    intros [=]; subst. depelim H1. reflexivity.
  Qed.

  (* Working in the total space is equivalent to transporting *)
  Lemma eq_rew {n m} (e : n = m) (v : vector n) (v' : vector m) : (n, v) = (m, v') <-> rew [vector] e in v = v'.
  Proof.
    split; destruct e => h; noconf h => //.
  Qed.

  Lemma to_total {n} (v v' : vector n) : v = v' <-> (n, v) = (n, v').
  Proof.
    now rewrite (eq_rew eq_refl).
  Qed.

  (* One can make toplevel transports disappear! *)
  Lemma simpl_rew {n n'} (e : n = n') (v : vector n) : (n', rew [vector] e in v) = (n, v).
  Proof.
    destruct e; now cbn.
  Qed.

  (** Now the usual theory of append *)
  Lemma app_assoc {n m k} (v : vector n) (w : vector m) (x : vector k) : 
    (_, (v ++ w) ++ x) = (_, v ++ (w ++ x)).
  Proof.
    funelim (app v w); cbn; simp app => //.
    now apply eq_cons.
  Qed.

  Lemma app_nil_r {n} (v1 : vector n) : (_, v1 ++ []) = (_, v1).
  Proof. 
    induction v1; simp app => //=.
    now apply eq_cons.
  Qed.
 
  (* Vrev using append or tail recursive version.  *)
  Equations vrev {n} (v : vector n) : vector n :=
    | [] => []
    | Vcons (n:=n) x xs => rew Nat.add_1_r n in app (vrev xs) (x :: []).

  (* The irrelevant obligations are filled by the default Program tactic here. *)
  Equations vrev_acc {n m} (v : vector n) (acc : vector m): vector (n + m) :=
    | [], acc => acc
    | x :: xs, acc => rew _ in vrev_acc xs (x :: acc).

  (* Getting back the "natural" index *)
  Definition vrev_tail {n} (v : vector n) : vector n := 
    rew [vector] (Nat.add_0_r n) in (vrev_acc v Vnil).

  (* These simplification lemmas along with the congruence lemma below could be generically derived. 
    They essentially say that index information can be moved between the input and output 
    and correspond to lemmas on lists like:
    length (append v w) = length v + length w.
  *)
  Lemma app_rew_l {n n' m} (e : n = n') (v : vector n) (w : vector m) :
    (n' + m, (rew [vector] e in v) ++ w) = (n + m, v ++ w).
  Proof.
    now destruct e.
  Qed.

  Lemma app_rew_r {n m m'} (e : m = m') (v : vector n) (w : vector m) :
    (n + m', v ++ (rew [vector] e in w)) = (n + m, v ++ w).
  Proof.
    now destruct e.
  Qed.

  Lemma vrev_rew {n n'} (e : n = n') (v : vector n) :
    (n', vrev (rew [vector] e in v)) = (n, vrev v).
  Proof.
    now destruct e.
  Qed.

  (* This uses provable UIP as well *)
  Lemma congr_append {n m n' m'} (v : vector n) (w : vector m) (v' : vector n') (w' : vector m') :
    (n, v) = (n', v') ->
    (m, w) = (m', w') ->
    (n + m, v ++ w) = (n' + m', v' ++ w').
  Proof.
    move=> [=] e; destruct e => h; noconf h.
    now move=> [=] e; destruct e => h; noconf h.
  Qed.

  (* The tail rec version and its relation to append *)
  Lemma vrev_acc_spec {n m} (v : vector n) (w : vector m) : (n + m, vrev_acc v w) = (n + m, vrev v ++ w) :> Σ n, vector n.
  Proof.
    induction v in m, w |- *; cbn => //.
    simp vrev vrev_acc.
    now rewrite simpl_rew (app_rew_l (n' := S n)) IHv app_assoc.
  Qed. 

  Lemma vrev_vrev_tail {n} (v : vector n) : vrev_tail v = vrev v.
  Proof.
    rewrite /vrev_tail. apply eq_rew. 
    now rewrite vrev_acc_spec app_nil_r.
  Qed.
  
  From Stdlib Require Import Lia.


  Lemma vrev_app {n m} (v : vector n) (w : vector m) : (n + m, vrev (v ++ w)) = (m + n, vrev w ++ vrev v).
  Proof.
    induction v; cbn; simp vrev app => //=.
    - now rewrite app_nil_r.
    - rewrite simpl_rew app_rew_r -app_assoc.
      apply congr_append => //.
  Qed.

  Lemma vrev_acc_invol {n} (v : vector n) : vrev (vrev v) = v.
  Proof.
    induction v; simp vrev => //=.
    apply to_total.
    now rewrite vrev_rew vrev_app IHv app_rew_l.
  Qed.

  Lemma vrev_tail_invol {n} (v : vector n) : vrev_tail (vrev_tail v) = v.
  Proof.
    now rewrite !vrev_vrev_tail vrev_acc_invol.
  Qed.

  Print Assumptions vrev_tail_invol. (* No axioms *)
  
End vectors.