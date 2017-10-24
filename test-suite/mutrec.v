Require Import Equations.Equations.

Inductive term : Set :=
| Var (n : nat)
| App (t : term) (l : term_list)

with term_list : Set :=
| nilt : term_list
| const : term -> term_list -> term_list.

Equations id_term (t : term) : term := {
id_term (Var n) := Var n;
id_term (App t l) := App (id_term t) (id_tlist l) }

id_tlist (t : term_list) : term_list := {
  id_tlist nilt := nilt;
  id_tlist (const t tl) := const (id_term t) (id_tlist tl) }.

Next Obligation.
  split.
  fix ft 1 with (ftl (l : term_list) {struct l} : id_term_ind_1 l (id_tlist l));
              (destruct t || destruct l); constructor; auto.
  all:(fix ftl 1 with (ft (t : term) {struct t} : id_term_ind t (id_term t));
       (destruct t || destruct l); constructor; auto).
Defined.

Next Obligation.
  pose (id_term_ind_comb P P0).
  assert (and (forall (t t0 : term) (_ : id_term_ind t t0), P t t0)
              (forall (t t0 : term_list) (_ : id_term_ind_1 t t0), P0 t t0)).
  apply a; eauto.
  clear a. destruct H.
  pose (id_term_ind_fun). destruct_conjs.
  split; intros; typeclasses eauto with id_term funelim.
Defined.