(* -*- compile-command: "COQBIN=~/research/coq/trunk/bin/ make -k -C .. src/equations_plugin.cma src/equations_plugin.cmxs" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id: equations.ml4 11996 2009-03-20 01:22:58Z letouzey $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Coqlib

open Tactics
open Refiner
open Tacticals
open Tacmach

open Common

let coq_sigma = Lazy.lazy_from_fun Coqlib.build_sigma_type

let mkSig (n, c, t) =
  mkApp ((Lazy.force coq_sigma).Coqlib.typ, [| c; mkLambda (n, c, t) |])

let constrs_of_coq_sigma env sigma t alias = 
  let s = Lazy.force coq_sigma in
  let rec aux proj c ty =
    match kind_of_term c with
    | App (f, args) when eq_constr f s.Coqlib.intro && 
	Array.length args = 4 -> 
	(match kind_of_term args.(1) with
	| Lambda (n, b, t) ->
	    let projargs = [| args.(0); args.(1); proj |] in
	    let p1 = mkApp (s.Coqlib.proj1, projargs) in
	    let p2 = mkApp (s.Coqlib.proj2, projargs) in
	      (n, args.(2), p1, args.(0)) :: aux p2 args.(3) t
	| _ -> raise (Invalid_argument "constrs_of_coq_sigma"))
    | _ -> [(Anonymous, c, proj, ty)]
  in aux alias t (Typing.type_of env sigma t)

let decompose_coq_sigma t = 
  let s = Lazy.force coq_sigma in
    match kind_of_term t with
    | App (f, args) when eq_constr f s.Coqlib.typ && 
	Array.length args = 2 -> Some (args.(0), args.(1))
    | _ -> None

let decompose_indapp f args =
  match kind_of_term f with
  | Construct (ind,_) 
  | Ind ind ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = array_chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let sigmaize env sigma f =
  let ty = Retyping.get_type_of env sigma f in
  let ctx, concl = decompose_prod_assum ty in
  let argtyp, letbinders, make = Subtac_command.telescope ctx in
  let tyargs =
    [| argtyp; mkLambda (Name (id_of_string "index"), argtyp, 
			it_mkProd_or_LetIn 
			  (mkApp (lift (succ (List.length letbinders)) f, 
				 rel_vect 0 (List.length letbinders)))
			  letbinders) |]
  in
  let tysig = mkApp ((Lazy.force coq_sigma).typ, tyargs) in
  let indexproj = mkApp ((Lazy.force coq_sigma).proj1, tyargs) in
  let valproj = mkApp ((Lazy.force coq_sigma).proj2, tyargs) in
  let indices = 
    list_map_i (fun i (_, b, _) -> lift (-i) (Option.get b)) 0 (List.rev letbinders)
  in
  let valsig args v = 
    mkApp ((Lazy.force coq_sigma).intro, 
	  Array.append tyargs [| substl (rev args) make; v |])
  in indices, indexproj, valproj, valsig, tysig

let mk_pack env sigma ty =
  match kind_of_term ty with
  | App (f, args) ->
      let f, args = decompose_indapp f args in
      let args = Array.to_list args in
	(match args with
	| [] -> ((fun v -> v), f)
	| _ -> 
	    let _, _, _, valsig, tysig = sigmaize env sigma f in
	      valsig args, tysig)
  | _ -> ((fun v -> v), ty)

let generalize_sigma env sigma c packid =
  let ty = Retyping.get_type_of env sigma c in
  let value, typ = mk_pack env sigma ty in
  let valsig = value c in
  let setvar = letin_tac None (Name packid) valsig (Some typ) nowhere in
  let geneq = generalize [mkCast (mkRefl typ (mkVar packid), 
					 DEFAULTcast, mkEq typ (mkVar packid) valsig)] in
  let clear = clear_body [packid] in
  let movetop = move_hyp true packid (Tacexpr.MoveToEnd false) in
    tclTHENLIST [setvar; geneq; clear; movetop]

let pattern_sigma c hyp gl =
  let terms = constrs_of_coq_sigma (pf_env gl) (project gl) c (mkVar hyp) in
  let pat = Pattern.pattern_of_constr (project gl) in
  let projs = map (fun (x, t, p, rest) -> (snd (pat t), p)) terms in
  let projabs = tclTHENLIST (map (fun (t, p) -> change (Some t) p onConcl) projs) in
    projabs gl
      
TACTIC EXTEND pack
[ "pack" hyp(id) "as" ident(packid) ] -> [ fun gl ->
  let (valsig, typesig) = mk_pack (pf_env gl) (project gl) (pf_get_hyp_typ gl id) in
  let simpl = Tacred.simpl (pf_env gl) (project gl) in
  let typesig = simpl typesig in
  let term = simpl (valsig (mkVar id)) in
    tclTHENLIST [letin_tac None (Name packid) term (Some typesig) allHypsAndConcl;
		 pattern_sigma term packid] gl ]
END

let curry_hyp c t =
  let na, dom, concl = destProd t in
    match decompose_coq_sigma dom with
    | None -> None
    | Some (ty, pred) ->
	let (n, idx, dom) = destLambda pred in
	let newctx = [(na, None, dom); (n, None, idx)] in
	let tuple = mkApp ((Lazy.force coq_sigma).intro,
			  [| lift 2 ty; lift 2 pred; mkRel 2; mkRel 1 |])
	in
	let term = it_mkLambda_or_LetIn (mkApp (c, [| tuple |])) newctx in
	let typ = it_mkProd_or_LetIn (subst1 tuple concl) newctx in
	  Some (term, typ)
	    
TACTIC EXTEND curry
[ "curry" hyp(id) ] -> [ fun gl ->
  match curry_hyp (mkVar id) (pf_get_hyp_typ gl id) with
  | Some (prf, typ) -> 
      cut_replacing id typ (Tacmach.refine_no_check prf) gl
  | None -> tclFAIL 0 (str"No currying to do in" ++ pr_id id) gl ]
END

TACTIC EXTEND pattern_tele
[ "pattern_tele" constr(c) ident(hyp) ] -> [ fun gl ->
  let settac = letin_tac None (Name hyp) c None onConcl in
    tclTHENLIST [settac; pattern_sigma c hyp] gl ]
END
