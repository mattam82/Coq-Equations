Require Import Equations.Equations.

Module two.
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

Definition test := id_term_elim.
End two.


Module three.

Inductive term : Set :=
| Var (n : nat)
| App (t : term) (l : term_list)
| App2 (t : term) (l : term_list')

with term_list : Set :=
| nilt : term_list
| const : term -> term_list -> term_list

with term_list' : Set :=
| nilt' : term_list'
| const' : term -> term_list' -> term_list'.

Equations id_term (t : term) : term := {
id_term (Var n) := Var n;
id_term (App t l) := App (id_term t) (id_tlist l);
id_term (App2 t l) := App (id_term t) (id_tlist' l) }

with id_tlist (t : term_list) : term_list := {
  id_tlist nilt := nilt;
  id_tlist (const t tl) := const (id_term t) (id_tlist tl) }

with id_tlist' (t : term_list') : term_list := {
  id_tlist' nilt' := nilt ;
  id_tlist' (const' t tl) := let t' := id_term t in
                             let l' := id_tlist' tl in const t' l' }.

Definition test := id_term_elim.
End three.

Module four.

Inductive term : Set :=
| Var (n : nat)
| App (t : term) (l : term_list)
| App2 (t : term) (l : term_list')

with term_list : Set :=
| nilt : term_list
| const : term -> term_list -> term_list

with term_list' : Set :=
| nilt' : term_list'
| const' : term -> term_list' -> term_list'.

Equations id_term (t : term) : term := {
id_term (Var n) := Var n;
id_term (App t l) := App (id_term t) (id_tlist l);
id_term (App2 t l) := App (id_term t) (id_tlist' l) }

with id_tlist (t : term_list) : term_list := {
  id_tlist nilt := nilt;
  id_tlist (const t tl) := const (id_term t) (id_tlist tl) }

with id_tlist' (t : term_list') : term_list := {
  id_tlist' nilt' := nilt ;
  id_tlist' (const' t tl) := let t' := id_term t in
                             let l' := id_tlist' tl in const t' l' }

with bla (t : term) : term := {
bla (Var n) := Var 0;
bla (App t l) := App (bla t) (id_tlist l);
bla (App2 t l) := App (bla t) (id_tlist' l) }.

Definition test := id_term_elim.
End four.