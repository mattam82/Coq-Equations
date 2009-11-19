(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Equations.DepElim.

(** The [FunctionalInduction f] typeclass is meant to register functional induction
   principles associated to a function [f]. Such principles are automatically 
   generated for definitions made using [Equations]. *)

Class FunctionalInduction {A : Type} (f : A) :=
  { fun_ind_prf_ty : Prop; fun_ind_prf : fun_ind_prf_ty }.

(** The tactic [funind c Hc] applies functional induction on the application 
   [c] which must be of the form [f args] where [f] has a [FunctionalInduction]
   instance. [Hc] is the name given to the call, used to generate hypothesis names. *)

Ltac funind c Hcall := 
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_ind_prf (f:=f)) in
        (let prf := eval simpl in x in
         let p := context C [ prf ] in
         let prf := fresh in
         let call := fresh in
           assert(prf:=p) ;
           (* Abstract the call *)
           set(call:=c) in *; generalize (refl_equal : call = c); clearbody call ; intro Hcall ;
           (* Now do dependent elimination and simplifications *)
           dependent induction prf ; simplify_IH_hyps ; 
           (* Use the simplifiers for the constant to get a nicer goal. *)
           try simpc f in * ; try on_last_hyp ltac:(fun id => simpc f in id ; noconf id))
        || fail 1 "Internal error in funind"
  end || fail "Maybe you didn't declare the functional induction principle for" c.

Ltac funind_call f H :=
  on_call f ltac:(fun call => funind call H).

(** The [FunctionalElimination f] class declares elimination principles produced
   from the functional induction principle for [f] to be used directly to eliminate
   a call to [f]. This is the preferred method of proving results about a function. 
   NOTE: the arguments of the call should all be variables to ensure the goal is 
   not weakened (no dependent elimination yet).
   *)

Class FunctionalElimination {A : Type} (f : A) :=
  { fun_elim_ty : Prop; fun_elim : fun_elim_ty }.

Ltac funelim c :=
  match c with
    | appcontext C [ ?f ] =>
      let elim := constr:(fun_elim (f:=f)) in
        pattern_call c ; apply elim ; clear ; simplify_dep_elim;
          simplify_IH_hyps
  end.
