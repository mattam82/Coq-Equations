From Equations Require Import EqDec DepElim NoConfusion.

(** Tactic to solve EqDec goals, destructing recursive calls for the recursive 
  structure of the type and calling instances of eq_dec on other types. *)
Hint Extern 2 (@EqDecPoint ?A ?x) =>
  match goal with
    [ H : forall y, { x = _ } + { _ <> _ } |- _ ] => exact H
  end : typeclass_instances.

Ltac eqdec_one x y :=
  let good := intros -> in
  let contrad := intro Hn; right; red; simplify_dep_elim; apply Hn; reflexivity in
  try match goal with
       | [ H : forall z, dec_eq x z |- _ ] =>
         case (H y); [good|contrad]
        | [ H : forall z, { x = z } + { _ } |- _ ] =>
          case (H y); [good|contrad]
         | _ =>
           tryif unify x y then idtac (* " finished " x y *)
           else (case (eq_dec x y); [good|contrad])
  end.

Ltac eqdec_loop t u :=
  match t with
  | appcontext C [ ?t ?x ] =>
    match u with
    | appcontext C [ ?u ?y] => eqdec_loop t u; eqdec_one x y
    end
   | _ => eqdec_one t u
  end.

Ltac eqdec_proof := try red; intros;
  match goal with
    |- dec_eq ?x ?y =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- dec_eq ?x ?y => eqdec_loop x y
    end
   | |- { ?x = ?y } + { _ } =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- { ?x = ?y } + { _ } => eqdec_loop x y
    end
  end; try solve[left; reflexivity | right; red; simplify_dep_elim].

(** Standard instances. *)

Instance unit_eqdec : EqDec unit. 
Proof. eqdec_proof. Defined.

Instance bool_eqdec : EqDec bool.
Proof. eqdec_proof. Defined.

Instance nat_eqdec : EqDec nat.
Proof. eqdec_proof. Defined.

Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. eqdec_proof. Defined.

Instance sum_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (A + B).
Proof. eqdec_proof. Defined.

Instance list_eqdec {A} `(EqDec A) : EqDec (list A). 
Proof. eqdec_proof. Defined.

Instance sigma_eqdec {A B} `(EqDec A) `(forall x, EqDec (B x)) : EqDec {x : A & B x}.
Proof. eqdec_proof. Defined.
