From Equations Require Import Equations.
Check le.
Require Import Relations Wellfounded.

Section Image.
  Context {A B : Type} (f : A -> B).

  Inductive Im : B -> Type :=
  | im x : Im (f x).

  Inductive ImI : forall (b : B) (im : Im b), Type :=
  | imf x : ImI (f x) (im x).

  Derive Invert for ImI.
  Print invert_ImI.
End Image.

Section Vector.
  Inductive vector (A : Type) : nat -> Type :=
  | vnil : vector A 0
  | vcons (a : A) (n : nat) (v : vector A n) : vector A (S n).

  Derive Invert for vector.

  Set Printing Universes.
  Print invert_vector. 
End Vector.

Inductive SFalse : SProp :=.
Inductive STrue : SProp := sI.

(** This is a bit of a hack for the moment, only the sort, true and false propositions
    are used by the Derive Invert command. *)
Equations Logic
          SProp Id Id_rect Id_rect_r Id_rect_dep_r
          SFalse STrue sI prod pair
          relation clos_trans WellFounded well_founded.

(** Definable but squashed *)
Inductive le : nat -> nat -> SProp :=
| le_0 n : le 0 n
| le_S n m (H : le n m) : le (S n) (S m).

Fail Check (fun m n (H : le m n) => match H with le_0 n => true | le_S m n H => false end).

Derive Invert for le.
Print invert_le.

(** The induction principle is not generated automatically yet. *)

Definition le_rect
  (P : forall n m : nat, invert_le n m -> Type) :
  (forall n, P 0 n sI) ->
  (forall (m n : nat) (H : invert_le m n), P m n H -> P (S m) (S n) H) ->
  forall (m n : nat) (H : invert_le m n), P m n H.
Proof.
  induction m; auto. destruct n; simpl; auto. intros [].
Qed.

Check (fun m n (H : invert_le m n) => le_rect (fun _ _ _ => bool) (fun n => true) (fun _ _ _ _ => false) m n H).
