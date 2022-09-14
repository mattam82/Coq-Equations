open Locusops
open Constr
open Names
open Tactics
open Equations_common
open EConstr

let decompose_app h h' c =
  Proofview.Goal.enter begin fun gl ->
    let f, args = EConstr.decompose_app (Proofview.Goal.sigma gl) c in
    let fty = Tacmach.pf_hnf_type_of gl f in
    let flam = mkLambda (Context.nameR (Id.of_string "f"), fty, mkApp (mkRel 1, Array.of_list args)) in
      (Proofview.tclTHEN (letin_tac None (Name h) f None allHyps)
         (letin_tac None (Name h') flam None allHyps)) end

let autounfold_ref gr =
  let db = match gr with
    | GlobRef.ConstRef c -> Names.Label.to_string (Names.Constant.label c)
    | _ -> assert false
  in Eauto.autounfold ["core";db] Locusops.onConcl


open Proofview.Goal
open Proofview.Notations

(** [refine_ho c]

  Matches a lemma [c] of type [∀ ctx, ty] with a conclusion of the form
  [∀ ctx, ?P args] using second-order matching on the problem
  [ctx |- ?P args = ty] and then refines the goal with [c]. *)

let refine_ho c =
  enter begin fun gl ->
    let env = env gl in
    let sigma = sigma gl in
    let concl = concl gl in
    let ty = Tacmach.pf_apply Retyping.get_type_of gl c in
    let ts = TransparentState.full in
    let flags = Evarconv.default_flags_of ts in
    let evd = ref (to_evar_map sigma) in
    let rec aux env concl ty =
      match kind sigma concl, kind sigma ty with
      | Prod (na, b, t), Prod (na', b', t') ->
         (match Evarconv.unify_delay ~flags env !evd b b' with
          | exception Evarconv.UnableToUnify _ -> error "Products do not match"
          | evm -> evd := evm;
                        aux (push_rel (of_tuple (na,None,b)) env) t t')
      (* | _, LetIn (na, b, _, t') -> *)
      (*    aux env t (subst1 b t') *)
      | _, App (ev, args) when isEvar sigma ev ->
         let (evk, subst as ev) = destEvar sigma ev in
         let sigma = !evd in
         let sigma,ev = evar_absorb_arguments env sigma ev (Array.to_list args) in
         let evargs = Evd.expand_existential sigma ev in
         let argtest = Evarconv.default_occurrence_test ~allowed_evars:Evarsolve.AllowedEvars.all ts in
         let argoccs = List.map
             (fun _ -> Evarconv.Unspecified Evd.Abstraction.Abstract) evargs in
         let sigma, b = Evarconv.second_order_matching flags env sigma ev (argtest,argoccs) concl in
         if not b then
           error "Second-order matching failed"
         else Proofview.Unsafe.tclEVARS sigma <*>
                Refine.refine ~typecheck:false (fun sigma -> (sigma, c))
      | _, _ -> error "Couldn't find a second-order pattern to match"
    in aux env concl ty end
