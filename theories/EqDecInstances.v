From Equations Require Import EqDec DepElim NoConfusion.

(** Tactic to solve EqDec goals, destructing recursive calls for the recursive 
  structure of the type and calling instances of eq_dec on other types. *)

Ltac eqdec_loop t u :=
  (left; reflexivity) || 
  (solve [right; red; simplify_dep_elim]) ||
  (let x := match t with
             | appcontext C [ _ ?x ] => constr:x
             end
    in
    let y := match u with
             | appcontext C [ _ ?y ] => constr:y
             end
    in
    let contrad := intro Hn; right; red; simplify_dep_elim; apply Hn; reflexivity in
    let good := intros ->;
      let t' := match t with
                | appcontext C [ ?x _ ] => constr:x
                end
      in
      let u' := match u with
                | appcontext C [ ?y _ ] => constr:y
                end
      in
      try (eqdec_loop t' u')
    in
    match goal with
      [ H : forall z, dec_eq x z |- _ ] =>
      case (H y); [good|contrad]
    | [ H : forall z, { x = z } + { _ } |- _ ] =>
      case (H y); [good|contrad]
    | _ => case (eq_dec x y); [good|contrad]
    end) || idtac.

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
  end.

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
