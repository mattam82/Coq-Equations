Require Import Equations.Equations.

Inductive term : Set :=
| Var (n : nat)
| App (t : term) (l : list term).

Equations id_term (t : term) : term := {
id_term (Var n) := Var n;
id_term (App t l) := App (id_term t) (id_tlist l) }

where id_tlist (t : list term) : list term := {
  id_tlist nil := nil;
  id_tlist (cons t ts) := cons (id_term t) (id_tlist ts) }.
  (* id_tlist t := List.map id_term t }. *)

Next Obligation.
  assert (forall t, id_term_ind t (id_term t)).
  fix 1. destruct t; constructor; auto.
  revert l. fix 1. destruct l; constructor; auto.
  split; auto.

  fix 1. destruct t; constructor; auto.
Defined.

Next Obligation.
  pose (id_term_ind_comb P P0).
  edestruct a; eauto.
  split; intros; eauto with funelim.
  apply H.
  apply id_term_ind_fun.
  apply H0.
  apply id_term_ind_fun.
Defined.

Check eq_refl : List.map id_term = id_tlist.