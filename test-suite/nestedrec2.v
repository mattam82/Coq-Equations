Require Import Equations.Equations.
Require Import Arith.
Require Import Compare_dec.

Inductive term : Set :=
| Var (n : nat)
| Lam (t : term)
| App (t : term) (l : list term).

Equations subst_var (k : nat) (u : term) (t : nat) : term :=
  subst_var k u n <= k ?= n =>
   { | Eq => u;                                                                
     | Gt => Var n;
     | Lt => Var (pred n) }.

Equations subst_term (k : nat) (u : term) (t : term) : term := {
subst_term k u (Var n) => subst_var k u n;
subst_term k u (Lam t) => Lam (subst_term (S k) u t);
subst_term k u (App t l) := App (subst_term k u t) (subst_tlist k u l) }

where(struct t) subst_tlist (k : nat) (u : term) (t : list term) : list term := {
  subst_tlist k u nil := nil;
  subst_tlist k u (cons t ts) := cons (subst_term k u t) (subst_tlist k u ts) }.
  (* id_tlist t := List.map id_term t }. *)

Next Obligation.
  assert (forall k u t, subst_term_ind k u t (subst_term k u t)).
  fix 3. destruct t; constructor; auto.
  revert k u l. fix 3. destruct l; constructor; auto.
  split; auto.

  fix 3. destruct t; constructor; auto.
Defined.

Next Obligation.
  pose (subst_term_ind_comb P P0).
  edestruct a; eauto.
  split; intros; eauto with funelim.
  apply H.
  apply subst_term_ind_fun.
  apply H0.
  apply subst_term_ind_fun.
Defined.

Lemma subst_subst k u t : subst_term k u t = subst_term k u t.
Proof.
  revert k u t.
  refine (proj1 (subst_term_elim (fun k u t c => c = c) (fun k u l c => c = c) _ _ _ _ _));
  trivial.
Qed.