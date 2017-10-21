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
  revert t. fix 1. destruct t. constructor.
  constructor. apply id_term_ind_fun_obligation.
  clear t; revert l. fix 1.
  destruct l. constructor.
  constructor. auto. auto.
Defined.
  
  