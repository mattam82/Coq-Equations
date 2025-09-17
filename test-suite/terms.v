From Equations.Prop Require Import Equations.
From Stdlib Require Import List.

Inductive term :=
| Var : nat -> term
| App : term -> list term -> term
| Lam : term -> term.

#[derive(eliminator=no)] Equations term_size (t : term) : nat :=
term_size (Var n) := 0;
term_size (App f l) := S (List.fold_left (fun acc x => max acc (term_size x)) l (term_size f));
term_size (Lam f) := S (term_size f).

(** TODO: recognize recursive call under lambda abstraction *)
#[derive(eliminator=no)]
Equations subst (t : term) (k : nat) (u : term) : term :=
subst t k (Var n) := if Nat.eqb k n then t else Var n;
subst t k (App f l) := App (subst t k f) (List.map (fun x => subst t k x) l);
subst t k (Lam f) := Lam (subst t (S k) f).


