open Locusops
open Term
open Names
open Tactics
open Equations_common

let decompose_app h h' c =
  Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let f, args = decompose_app c in
    let fty = Tacmach.New.pf_hnf_type_of gl f in
    let flam = mkLambda (Name (id_of_string "f"), fty, mkApp (mkRel 1, Array.of_list args)) in
      (Proofview.tclTHEN (letin_tac None (Name h) f None allHyps)
         (letin_tac None (Name h') flam None allHyps)) }

let autounfold_ref gr =
  let db = match gr with
    | Globnames.ConstRef c -> Names.Label.to_string (Names.con_label c)
    | _ -> assert false
  in Eauto.autounfold ["core";db] Locusops.onConcl


open Proofview.Goal
open Proofview.Notations

(** [refine_ho c]

  Matches a lemma [c] of type [∀ ctx, ty] with a conclusion of the form
  [∀ ctx, ?P args] using second-order matching on the problem
  [ctx |- ?P args = ty] and then refines the goal with [c]. *)

let refine_ho c =
  nf_enter { enter = fun gl ->
    let env = env gl in
    let sigma = sigma gl in
    let concl = concl gl in
    let ty = Tacmach.New.pf_apply Retyping.get_type_of gl c in
    let ts = Names.full_transparent_state in
    let evd = ref (to_evar_map sigma) in
    let rec aux env concl ty =
      match kind_of_term concl, kind_of_term ty with
      | Prod (na, b, t), Prod (na', b', t') ->
         let ok = Evarconv.e_conv ~ts env evd b b' in
         if not ok then
           error "Products do not match"
         else aux (Environ.push_rel (of_tuple (na,None,b)) env) t t'
      (* | _, LetIn (na, b, _, t') -> *)
      (*    aux env t (subst1 b t') *)
      | _, App (ev, args) when isEvar ev ->
         let (evk, subst as ev) = destEvar ev in
         let sigma = !evd in
         let sigma,ev = evar_absorb_arguments env sigma ev (Array.to_list args) in
         let argoccs = CArray.map_to_list (fun _ -> None) (snd ev) in
         let sigma, b = Evarconv.second_order_matching ts env sigma ev argoccs concl in
         if not b then
           error "Second-order matching failed"
         else Proofview.Unsafe.tclEVARS sigma <*>
                Refine.refine ~unsafe:true { Sigma.run = fun sigma -> Sigma.here c sigma }
      | _, _ -> error "Couldn't find a second-order pattern to match"
    in aux env concl ty }
