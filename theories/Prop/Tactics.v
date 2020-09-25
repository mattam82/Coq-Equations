(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
Require Import Equations.CoreTactics Equations.Prop.Classes Equations.Prop.DepElim
        Equations.Prop.Subterm Equations.Prop.FunctionalInduction.

Ltac Equations.Init.simpl_equations ::= Equations.Prop.DepElim.simpl_equations.
Ltac Equations.Init.simplify_equalities ::= Equations.Prop.DepElim.simplify_dep_elim.
Ltac Equations.Init.depelim H ::= Equations.Prop.DepElim.depelim H.
Ltac Equations.Init.depind H ::= Equations.Prop.DepElim.depind H.
Ltac Equations.Init.dep_elim H ::= Equations.Prop.DepElim.dep_elim H.
Ltac Equations.Init.noconf H ::= Equations.Prop.DepElim.noconf H.
Ltac Equations.Init.funelim_constr H ::= funelim_constr H.
Ltac Equations.Init.apply_funelim H ::= Equations.Prop.FunctionalInduction.apply_funelim H.

(** Tactic to solve EqDec goals, destructing recursive calls for the recursive
  structure of the type and calling instances of eq_dec on other types. *)
Hint Extern 2 (@EqDecPoint ?A ?x) =>
  lazymatch goal with
  | [ H : forall y, { x = _ } + { _ <> _ } |- _ ] => exact H
  | [ H : forall y, dec_eq x y |- _ ] => exact H
  end : typeclass_instances.

Ltac eqdec_one x y :=
  let good := intros -> in
  let contrad := let Hn := fresh in
   intro Hn; right; red; simplify_dep_elim; apply Hn; reflexivity in
  try match goal with
       | [ H : forall z, dec_eq x z |- _ ] =>
         case (H y); [good|contrad]
        | [ H : forall z, { x = z } + { _ } |- _ ] =>
          case (H y); [good|contrad]
         | _ =>
           tryif unify x y then idtac (* " finished " x y *)
           else (case (eq_dec_point (x:=x) y); [good|contrad])
  end.

Ltac eqdec_loop t u :=
  match t with
  | context C [ ?t ?x ] =>
    match u with
    | context C [ ?u ?y] => eqdec_loop t u; eqdec_one x y
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

Ltac Equations.Init.solve_eqdec ::= eqdec_proof.
Ltac Equations.Init.solve_subterm ::= Equations.Prop.Subterm.solve_subterm.
Ltac Equations.Init.unfold_recursor ::= Equations.Prop.Subterm.unfold_recursor.
Ltac Equations.Init.unfold_recursor_ext ::= Equations.Prop.Subterm.unfold_recursor_ext.

Ltac solve_noconf_prf := intros;
  on_last_hyp ltac:(fun id => destruct id) ; (* Subtitute a = b *)
  on_last_hyp ltac:(fun id =>
                      destruct_sigma id;
                      destruct id) ; (* Destruct the inductive object a *)
  constructor.

Ltac solve_noconf_inv_eq a b :=
  destruct_sigma a; destruct_sigma b;
  destruct a ; depelim b; simpl in * |-;
  on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
  solve [constructor].

Ltac solve_noconf_inv := intros;
  match goal with
    |- ?R ?a ?b => destruct_sigma a; destruct_sigma b;
                   destruct a ; depelim b; simpl in * |-;
                 on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
                 solve [constructor]
  | |- @eq _ (?f ?a ?b _) _ => solve_noconf_inv_eq a b
  end.

Ltac solve_noconf_inv_equiv :=
  intros;
  (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => destruct id) ;
  (* Destruct the inductive object a *)
  on_last_hyp ltac:(fun id => destruct_sigma id; destruct id) ;
  simpl; constructor.

Ltac solve_noconf := simpl; intros;
    match goal with
      [ H : @eq _ _ _ |- @eq _ _ _ ] => try solve_noconf_inv_equiv
    | [ H : @eq _ _ _ |- _ ] => try solve_noconf_prf
    | [ |- @eq _ _ _ ] => try solve_noconf_inv
    end.

Ltac solve_noconf_hom_inv_eq a b :=
  destruct_sigma a; destruct_sigma b;
  destruct a ; depelim b; simpl in * |-;
  on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
  solve [constructor || simpl_equations; constructor].

Ltac solve_noconf_hom_inv := intros;
  match goal with
  | |- @eq _ (?f ?a ?b _) _ => solve_noconf_hom_inv_eq a b
  | |- ?R ?a ?b =>
    destruct_sigma a; destruct_sigma b;
    destruct a ; depelim b; simpl in * |-;
    on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
    solve [constructor || simpl_equations; constructor]
  end.

Ltac solve_noconf_hom_inv_equiv :=
  intros;
  (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => destruct id) ;
  (* Destruct the inductive object a using dependent elimination
     to handle UIP cases. *)
  on_last_hyp ltac:(fun id => destruct_sigma id; depelim id) ;
  simpl; simpl_equations; constructor.

Ltac solve_noconf_hom := simpl; intros;
    match goal with
      [ H : @eq _ _ _ |- @eq _ _ _ ] => try solve_noconf_hom_inv_equiv
    | [ H : @eq _ _ _ |- _ ] => try solve_noconf_prf
    | [ |- @eq _ _ _ ] => try solve_noconf_hom_inv
    end.

Ltac Equations.Init.solve_noconf ::= solve_noconf.
Ltac Equations.Init.solve_noconf_hom ::= solve_noconf_hom.
