(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Init Signature DepElim EqDec HSetInstances.

(** Alternative implementation of generalization using sigma types only,
   allowing to use K on decidable domains. *)

(* Use the new simplification. *)
(* FIXME Temporary location? *)
Ltac simplify_one_dep_elim' :=
match goal with
(* Do not put any part of the rhs in the hypotheses. *)
| |- let _ := block in _ => fail 1
| |- _ => simplify ?
(* Fallback for JMeq. *)
| |- @JMeq _ _ _ _ -> _ => refine (@simplification_heq _ _ _ _ _)
(* Trying with more primitive tactics. *)
| |- ?f ?x = ?g ?y -> _ => let H := fresh in progress (intros H ; injection H ; clear H)
| |- Id (?f ?x) (?g ?y) -> _ => let H := fresh in progress (intros H ; inversion H ; clear H)
| |- ?t = ?u -> _ => let hyp := fresh in
  intros hyp ; elimtype False ; discriminate
| |- Id ?t ?u -> _ => let hyp := fresh in
  intros hyp ; elimtype False ; solve [inversion hyp]
| |- ?x = ?y -> _ => let hyp := fresh in
  intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
    case hyp
| |- Id _ ?x ?y -> _ => let hyp := fresh in
  intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
    case hyp
| |- _ -> ?B => let ty := type of B in (* Works only with non-dependent products *)
  intro || (let H := fresh in intro H)
| |- forall x, _ =>
  let H := fresh x in intro H
| |- _ => intro
end.

Ltac simplify_dep_elim ::= repeat simplify_one_dep_elim'.

(** Decompose existential packages. *)

(* Definition sigT_elim {A} {P : A -> Type} {P0 : sigma _ P -> Type} : *)
(*   (forall (x : A) (p : P x), P0 (sigmaI P x p)) -> forall s, P0 s := sigma_rect P0. *)

Ltac decompose_exists id id' := hnf in id ;
  match type of id with
    | @sigma _ _ => let xn := fresh id "'" in
      destruct id as [xn id]; decompose_exists xn id; 
        cbv beta delta [ pr1 pr2 ] iota in id, id';
          decompose_exists id id'
    | _ => cbv beta delta [ pr1 pr2 ] iota in id, id'
  end.

(** Dependent generalization using existentials only. *)

Ltac generalize_sig_gen id cont :=
  let id' := fresh id in
  get_signature_pack id id';
  hnf in (value of id'); hnf in (type of id');
  lazymatch goal with
  | id' := ?v |- context[ id ] =>
    generalize (@idpath _ id' : v = id') ;
    clearbody id'; simpl in id';
    cont id id' id v
  | id' := ?v |- _ => 
    let id'1 := fresh id' in let id'2 := fresh id' in
    set (id'2 := pr2 id'); set (id'1 := pr1 id') in id'2;
    hnf in (value of id'1), (value of id'2);
    try red in (type of id'2);
    match goal with
      [ id'1 := ?t |- _ ] =>
      generalize (@idpath _ id'1 : t = id'1);
        clearbody id'2 id'1; clear id' id;
        try unfold signature in id'2; hnf in id'2; simpl in id'2;
        rename id'2 into id; cont id id id'1 t
    end
  end.

Ltac generalize_sig id cont :=
  generalize_sig_gen id
    ltac:(fun id id' id'1 t => (* Fails if id = id' *)
            try rename id into id', id' into id;
          cont id'1 id).

Ltac generalize_sig_vars id cont :=
  generalize_sig_gen id 
    ltac:(fun id id' id'1 t => move_after_deps id' t; revert_until id';
          rename id' into id; cont id'1 id).

Ltac Id_generalize_sig_gen id cont :=
  let id' := fresh id in
  get_signature_pack id id';
  hnf in (value of id'); hnf in (type of id');
  lazymatch goal with
  | id' := ?v |- context[ id ] =>
    generalize (@id_refl _ id' : Id id' id') ;
    unfold id' at 1;
    clearbody id'; simpl in id';
    cont id id' id' v
  | id' := ?v |- _ =>
    let id'1 := fresh id' in let id'2 := fresh id' in
    set (id'2 := pr2 id'); set (id'1 := pr1 id') in id'2;
    hnf in (value of id'1), (value of id'2);
    match goal with
    | [ id'1 := ?t |- _ ] =>
      generalize (@id_refl _ id'1 : Id t id'1);
        clearbody id'2 id'1;
        clear id' id; compute in id'2;
        rename id'2 into id; cont id id id'1 v
    end
  end.

Ltac Id_generalize_sig id cont :=
  Id_generalize_sig_gen id
    ltac:(fun id id' id'1 t => (* Fails if id = id' *)
            try rename id into id', id' into id;
          cont id'1 id).

Ltac Id_generalize_sig_vars id cont :=
  Id_generalize_sig_gen id 
    ltac:(fun id id' id'1 t => move_after_deps id' t; revert_until id';
          rename id' into id; cont id'1 id).

Ltac generalize_sig_dest id :=
  generalize_sig id ltac:(fun id id' => decompose_exists id id').

Ltac generalize_sig_vars_dest id :=
  generalize_sig_vars id ltac:(fun id id' => decompose_exists id id').

Ltac generalize_eqs_sig id :=
  (needs_generalization id ; generalize_sig_dest id) 
    || idtac.

Ltac generalize_eqs_vars_sig id :=
  (needs_generalization id ; generalize_sig_vars_dest id) 
    || idtac.

Ltac generalize_by_eqs id ::= generalize_eqs_sig id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars_sig id.

Require Import FunctionalInduction.

Ltac funelim c ::= funelim_sig_tac c ltac:(fun _ => idtac).
