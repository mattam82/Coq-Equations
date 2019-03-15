Set Warnings "-notation-overridden".

Set Universe Polymorphism.
Require Import Relations.
(** Switch to an equality in Type *)
Require Import Equations.Type.All.

Derive Signature for Id.

Definition nathset := _ : HSet nat.

(* Equations test_k (x : nat) (r : x = x) : r = r := *)
(*   test_k x id_refl := id_refl. *)


Equations foo (A : Type) (x : A) : A :=
foo A x := x.


Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature for fin.

Derive NoConfusion for nat.

Equations finp {n} (f : fin (S n)) : unit + fin n :=
  finp fz := inl tt;
  finp (fs f) := inr f.

Unset Universe Minimization ToSet.
Inductive vector@{i} (A : Type@{i}) : nat -> Type@{i} :=
| vnil : vector A 0
| vcons {n} : A -> vector A n -> vector A (S n).
Arguments vector A%type_scope n%nat_scope.
Arguments vnil {A}.
Arguments vcons {A%type_scope} {n%nat_scope} a v.
Derive Signature for vector.
Require Import Equations.Tactics Equations.Type.Tactics.

Set Universe Minimization ToSet.
Derive NoConfusionHom for vector.
Unset Universe Minimization ToSet.

Instance vector_eqdec@{i +|+} {A : Type@{i}} {n} `(EqDec@{i} A) : EqDec (vector A n).
Proof.
  intros. intros x. intros y. induction x.
  - left. now depelim y.
  - depelim y. Show Universes. Show Proof.
    pose proof (Classes.eq_dec a a0).
    dependent elimination X as [inl id_refl|inr Ha].
    -- specialize (IHx v).
       dependent elimination IHx as [inl id_refl|inr H].
       --- left; reflexivity.
       --- right. simplify *. now apply H.
    -- right; simplify *. now apply Ha. Show Proof.
Defined.

Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.

Derive NoConfusion for vect.

Derive Subterm for vector.
Hint Unfold vector_subterm : subterm_relation.
Import Sigma_Notations.
Section foo.
  Context {A B : Type}.
  (* Obligation Tactic := idtac. (* FIXME universe bug *) *)
  Set Equations Debug.
  Equations unzipv {n} (v : vector (A * B) n) : vector A n * vector B n
   by wf (signature_pack v) (@vector_subterm (A * B)) :=
  unzipv vnil := (vnil, vnil) ;
  unzipv (vcons (x, y) v) with unzipv v := {
    | (xs, ys) := (vcons x xs, vcons y ys) }.

(*     IsConstr
      ((fun (v0 : nat) (x : A) (y : B) (v : vector (A * B) v0) =>
        unzipv_obligations_obligation_1 v0 x y v
          (fun (x0 : nat) (x1 : vector (A * B) x0)
             (_ : vector_subterm (A * B) (signature_pack x1) (signature_pack (vcons (x, y) v))) =>
           unzipv x1)),
      {Top.1188 Top.1187 Top.1186 Top.1185 Top.1184 Top.1182} |= Top.1187 < Top.1185
                                                                 Top.695 <= Top.1187
                                                                 Top.696 <= Top.1187))]
*)
  Next Obligation.
    apply (unzipv_graph_mut P P0); auto.
    intros. apply X0. reflexivity. apply X.
    apply unzipv_graph_correct.
  Defined.
End foo.
