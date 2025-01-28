Require Import List ssreflect.
From Equations.Prop Require Import Equations.

Import ListNotations.

Equations ok_clause (e : nat -> option bool) (xs : list nat) : bool :=
  ok_clause e xs => ok_clause' e xs
    where
      ok_clause' (p : nat -> option bool) (l : list nat) : bool by struct l :=
      ok_clause' _ [] => true;
      ok_clause' p (x::l) with p x =>
      { | Some _ => ok_clause' p l;
        | _ => false }.

Lemma ok_clause_test p : ok_clause p [] = true.
Proof.
  now simp ok_clause.
Qed.

Lemma ok_clause_test' p cl : ok_clause p cl = false -> exists y, In y cl /\ p y = None.
Proof.
  apply (ok_clause_elim (fun e xs call => call = false -> exists y, In y xs /\ e y = None)
    (fun _ _ e xs call => call = false -> exists y, In y xs /\ e y = None)).
  all:try solve [cbn; try discriminate; firstorder eauto].
Qed.
