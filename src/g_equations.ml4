(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)


(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "equations_plugin"

open Equations_common
open Extraargs
open Eauto
open Locusops
open Term
open Names
open Tactics
open Pp
open Nameops
open Refiner
open Constrexpr
open Constrarg
   
TACTIC EXTEND decompose_app
[ "decompose_app" ident(h) ident(h') constr(c) ] -> [ 
  Proofview.Goal.enter { Proofview.Goal.enter = fun gl ->
    let f, args = decompose_app c in
    let fty = Tacmach.New.pf_hnf_type_of gl f in
    let flam = mkLambda (Name (id_of_string "f"), fty, mkApp (mkRel 1, Array.of_list args)) in
      (Proofview.tclTHEN (letin_tac None (Name h) f None allHyps)
  	 (letin_tac None (Name h') flam None allHyps)) }
  ]
END

TACTIC EXTEND autounfold_ref
| [ "autounfold_ref" reference(myref) ] -> [
    let db = match myref with
      | Globnames.ConstRef c -> Names.Label.to_string (Names.con_label c)
      | _ -> assert false
    in Eauto.autounfold ["core";db] Locusops.onConcl
  ]
END

(* TACTIC EXTEND abstract_match *)
(* [ "abstract_match" ident(hyp) constr(c) ] -> [ *)
(*   match kind_of_term c with *)
(*   | Case (_, _, c, _) -> letin_tac None (Name hyp) c None allHypsAndConcl *)
(*   | _ -> tclFAIL 0 (str"Not a case expression") *)
(* ] *)
(* END *)

(* TACTIC EXTEND autounfold_first *)
(* | [ "autounfold_first" hintbases(db) "in" hyp(id) ] -> *)
(*     [ autounfold_first (match db with None -> ["core"] | Some x -> x) (Some (id, InHyp)) ] *)
(* | [ "autounfold_first" hintbases(db) ] -> *)
(*     [ autounfold_first (match db with None -> ["core"] | Some x -> x) None ] *)
(* END *)

(* Sigma *)

open Proofview.Notations
open Proofview.Goal

TACTIC EXTEND get_signature_pack
[ "get_signature_pack" hyp(id) ident(id') ] -> [ 
  enter { enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma', sigsig, sigpack =
      Sigma_types.get_signature env (Sigma.to_evar_map sigma)
                                (Tacmach.New.pf_get_hyp_typ id gl) in
    Proofview.Unsafe.tclEVARS sigma' <*>
    letin_tac None (Name id') (mkApp (sigpack, [| mkVar id |])) None nowhere } ]
END
      
TACTIC EXTEND pattern_sigma
(* [ "pattern" "sigma" "left" hyp(id) ] -> [ *)
(*   Proofview.Goal.enter (fun gl -> *)
(*     let gl = Proofview.Goal.assume gl in *)
(*     let env = Proofview.Goal.env gl in *)
(*     let sigma = Proofview.Goal.sigma gl in *)
(*     let decl = Tacmach.New.pf_get_hyp id gl in *)
(*     let term = Option.get (Util.pi2 decl) in *)
(*     Sigma.pattern_sigma ~assoc_right:false term id env sigma) ] *)
| [ "pattern" "sigma" hyp(id) ] -> [
  enter { enter = fun gl ->
    let gl = Proofview.Goal.assume gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let decl = Tacmach.New.pf_get_hyp id gl in
    let term = Option.get (get_named_value decl) in
    Sigma_types.pattern_sigma ~assoc_right:true term id env
                              (Sigma.to_evar_map sigma) } ]
END

open Tacmach

let curry_hyp env sigma hyp t =
  let curry t =
    match kind_of_term t with
    | Prod (na, dom, concl) ->
       let ctx, arg = Sigma_types.curry na dom in
       let term = mkApp (mkVar hyp, [| arg |]) in
       let ty = Reductionops.nf_betaiota sigma (Vars.subst1 arg concl) in
       Some (it_mkLambda_or_LetIn term ctx, it_mkProd_or_LetIn ty ctx)
    | _ -> None
  in curry t

open CClosure.RedFlags

let red_curry () =
  let redpr pr = 
    fCONST (Projection.constant (Lazy.force pr)) in
  let reds = mkflags [redpr coq_pr1; redpr coq_pr2; fBETA; fMATCH] in
  Reductionops.clos_norm_flags reds

let curry_concl env sigma na dom codom =
  let ctx, arg = Sigma_types.curry na dom in
  let newconcl =
    let body = it_mkLambda_or_LetIn (Vars.subst1 arg codom) ctx in
    let inst = extended_rel_vect 0 ctx in
    red_curry () env sigma (it_mkProd_or_LetIn (mkApp (body, inst)) ctx) in
  let proj last decl (terms, acc) =
    if last then (acc :: terms, acc)
    else
      let term = mkProj (Lazy.force coq_pr1, acc) in
      let acc = mkProj (Lazy.force coq_pr2, acc) in
      (term :: terms, acc)
  in
  let terms, acc =
    match ctx with
    | hd :: (_ :: _ as tl) ->
       proj true hd (List.fold_right (proj false) tl ([], mkRel 1))
    | hd :: tl -> ([mkRel 1], mkRel 1)
    | [] -> ([mkRel 1], mkRel 1)
  in
  let sigma, ev = new_evar env sigma newconcl in
  let term = mkLambda (na, dom, mkApp (ev, CArray.rev_of_list terms)) in
  sigma, term

TACTIC EXTEND curry
[ "curry" hyp(id) ] -> [ 
  Proofview.V82.tactic 
    (fun gl ->
    let decl = pf_get_hyp gl id in
    let (na, body, ty) = to_named_tuple decl in
      match curry_hyp (pf_env gl) (project gl) id ty with
      | Some (prf, typ) ->
         (match body with
          | Some b ->
             let newprf = Vars.replace_vars [(id,b)] prf in
             tclTHEN (to82 (clear [id])) (to82 (Tactics.letin_tac None (Name id) newprf (Some typ) nowhere))
                     gl
          | None ->
	     (tclTHENFIRST (Proofview.V82.of_tactic (assert_before_replacing id typ))
		           (Tacmach.refine_no_check prf)) gl)
      | None -> tclFAIL 0 (str"No currying to do in " ++ pr_id id) gl) ]
| ["curry"] -> [ 
    nf_enter { enter = fun gl ->
      let env = Proofview.Goal.env gl in
      let concl = Proofview.Goal.concl gl in
      match kind_of_term concl with
      | Prod (na, dom, codom) ->
         Refine.refine
           { Sigma.run = fun sigma ->
             let sigma, prf = curry_concl env (Sigma.to_evar_map sigma) na dom codom in
             Sigma.here prf (Sigma.Unsafe.of_evar_map sigma) }
      | _ -> Tacticals.New.tclFAIL 0 (str"Goal cannot be curried") }
  ]
END

TACTIC EXTEND curry_hyps
[ "uncurry_hyps" ident(id) ] -> [ Sigma_types.uncurry_hyps id ]
END

TACTIC EXTEND uncurry_call
[ "uncurry_call" constr(c) ident(id) ] -> [
    enter { enter = fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        let sigma, term, ty = Sigma_types.uncurry_call env (Sigma.to_evar_map sigma) c in
        let sigma, _ = Typing.type_of env sigma term in
        Proofview.Unsafe.tclEVARS sigma <*>
          Tactics.letin_tac None (Name id) term (Some ty) nowhere }
      ]
END

(* TACTIC EXTEND pattern_tele *)
(* [ "pattern_tele" constr(c) ident(hyp) ] -> [ fun gl -> *)
(*   let settac = letin_tac None (Name hyp) c None onConcl in *)
(*     tclTHENLIST [settac; pattern_sigma c hyp] gl ] *)
(* END *)

(* Depelim *)

TACTIC EXTEND dependent_pattern
| ["dependent" "pattern" constr(c) ] -> [ 
  Proofview.V82.tactic (Depelim.dependent_pattern c) ]
END

TACTIC EXTEND dependent_pattern_from
| ["dependent" "pattern" "from" constr(c) ] ->
    [ Proofview.V82.tactic (Depelim.dependent_pattern ~pattern_term:false c) ]
END

TACTIC EXTEND pattern_call
[ "pattern_call" constr(c) ] -> [ of82 (Depelim.pattern_call c) ]
END

(* Noconf *)
let pr_sort_family _ _ _ s = mt ()

ARGUMENT EXTEND sort_family
PRINTED BY pr_sort_family
| [ "Type" ] -> [ InType ]
| [ "Prop" ] -> [ InProp ]
END

VERNAC COMMAND EXTEND Equations_Logic CLASSIFIED AS QUERY
| [ "Equations" "Logic" sort_family(s) global(eq) global(eqr) global(eq_case) global(eq_elim)
                global(z) global(o) global(ov) ] -> [
  let gr x = Lazy.from_val (Nametab.global x) in
  let open Misctypes in
  Equations_common.(set_logic { logic_eq_ty = gr eq;
				logic_eq_refl = gr eqr;
                                logic_eq_case = gr eq_case;
                                logic_eq_elim = gr eq_elim;
				logic_sort = s;
				logic_zero = gr z;
				logic_one = gr o;
				logic_one_val = gr ov})
  ]
END

(* TACTIC EXTEND dependent_generalize *)
(* | ["dependent" "generalize" hyp(id) "as" ident(id') ] ->  *)
(*     [ fun gl -> generalize_sigma (pf_env gl) (project gl) (mkVar id) id' gl ] *)
(* END *)
(* TACTIC EXTEND dep_generalize_force *)
(* | ["dependent" "generalize" "force" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:false ~force_dep:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars *)
(* | ["dependent" "generalize" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars_force *)
(* | ["dependent" "generalize" "force" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~force_dep:true ~generalize_vars:true id ] *)
(* END *)

TACTIC EXTEND needs_generalization
| [ "needs_generalization" hyp(id) ] -> 
    [ Proofview.V82.tactic (fun gl -> 
      if Depelim.needs_generalization gl id 
      then tclIDTAC gl
      else tclFAIL 0 (str"No generalization needed") gl) ]
END

(* Equations *)

open Extraargs
TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(destruct) tactic(tac) ] -> 
     [ of82 (Equations.solve_equations_goal (to82 (Tacinterp.tactic_of_value ist destruct))
                                            (to82 (Tacinterp.tactic_of_value ist tac))) ]
END

let wit_preident = Stdarg.wit_preident
TACTIC EXTEND simp
| [ "simp" ne_preident_list(l) clause(c) ] -> 
    [ of82 (Principles_proofs.simp_eqns_in c l) ]
| [ "simpc" constr_list(l) clause(c) ] -> 
    [ of82 (Principles_proofs.simp_eqns_in c (dbs_of_constrs l)) ]
END


(* let wit_r_equation_user_option : equation_user_option Genarg.uniform_genarg_type = *)
(*   Genarg.create_arg None "r_equation_user_option" *)

open Equations
open Syntax

open Pcoq.Prim

ARGUMENT EXTEND equation_user_option
PRINTED BY pr_r_equation_user_option
| [ "noind" ] -> [ OInd false ]
| [ "ind" ] -> [ OInd true ]
| [ "struct" ident(i) ] -> [ ORec (Some (loc, i)) ]
| [ "nostruct" ] -> [ ORec None ]
| [ "comp" ] -> [ OComp true ]
| [ "nocomp" ] -> [ OComp false ]
| [ "eqns" ] -> [ OEquations true ]
| [ "noeqns" ] -> [ OEquations false ]
END

ARGUMENT EXTEND equation_options
PRINTED BY pr_equation_options
| [ "(" ne_equation_user_option_list(l) ")" ] -> [ l ]
| [ ] -> [ [] ]
END

let pr_lident _ _ _ (loc, id) = pr_id id
       
ARGUMENT EXTEND lident
PRINTED BY pr_lident
| [ ident(i) ] -> [ (loc, i) ]
END


module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

type binders_argtype = Constrexpr.local_binder list Genarg.uniform_genarg_type

let pr_raw_binders2 _ _ _ l = mt ()
let pr_glob_binders2 _ _ _ l = mt ()
let pr_binders2 _ _ _ l = mt ()

(* let wit_binders_let2 : binders_let2_argtype = *)
(*   Genarg.create_arg "binders_let2" *)

let wit_binders2 : binders_argtype =
  Genarg.create_arg "binders2"

let binders2 : local_binder list Gram.entry =
  Pcoq.create_generic_entry Pcoq.uconstr "binders2" (Genarg.rawwit wit_binders2)

let _ = Pptactic.declare_extra_genarg_pprule wit_binders2
  pr_raw_binders2 pr_glob_binders2 pr_binders2

type deppat_equations_argtype = Syntax.pre_equation list Genarg.uniform_genarg_type

let wit_deppat_equations : deppat_equations_argtype =
  Genarg.create_arg "deppat_equations"

let pr_raw_deppat_equations _ _ _ l = mt ()
let pr_glob_deppat_equations _ _ _ l = mt ()
let pr_deppat_equations _ _ _ l = mt ()

let deppat_equations : Syntax.pre_equation list Gram.entry =
  Pcoq.create_generic_entry Pcoq.uvernac "deppat_equations" (Genarg.rawwit wit_deppat_equations)

let _ = Pptactic.declare_extra_genarg_pprule wit_deppat_equations
  pr_raw_deppat_equations pr_glob_deppat_equations pr_deppat_equations

type deppat_elim_argtype = Syntax.user_pat_expr list Genarg.uniform_genarg_type

let wit_deppat_elim : deppat_elim_argtype =
 Genarg.create_arg "deppat_elim"

let pr_raw_deppat_elim _ _ _ l = mt ()
let pr_glob_deppat_elim _ _ _ l = mt ()
let pr_deppat_elim _ _ _ l = mt ()

let deppat_elim : Syntax.user_pat_expr list Gram.entry =
  Pcoq.create_generic_entry Pcoq.utactic "deppat_elim" (Genarg.rawwit wit_deppat_elim)

let _ = Pptactic.declare_extra_genarg_pprule wit_deppat_elim
  pr_raw_deppat_elim pr_glob_deppat_elim pr_deppat_elim

type equations_argtype = pre_equations Genarg.uniform_genarg_type

let wit_equations : equations_argtype =
  Genarg.create_arg "equations"

let pr_raw_equations _ _ _ l = mt ()
let pr_glob_equations _ _ _ l = mt ()
let pr_equations _ _ _ l = mt ()

let equations : pre_equation where_clause list Gram.entry =
  Pcoq.create_generic_entry Pcoq.uvernac "equations" (Genarg.rawwit wit_equations)

let _ = Pptactic.declare_extra_genarg_pprule wit_equations
  pr_raw_equations pr_glob_equations pr_equations

open Glob_term
open Util
open Pcoq
open Prim
open Constr
open G_vernac
open Compat
open Tok

open Syntax

GEXTEND Gram
  GLOBAL: pattern deppat_equations deppat_elim binders2 equations lident;
 
  binders2 : 
     [ [ b = binders -> b ] ]
  ;
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  deppat_elim:
    [ [ "["; l = LIST0 lpatt SEP "|"; "]" -> l ] ]
  ;
  
  equation:
    [ [ id = identref; 	pats = LIST1 ipatt; r = rhs -> (Some id, SignPats pats, r)
      | "|"; pats = LIST1 lpatt SEP "|"; r = rhs -> (None, RefinePats pats, r) 
    ] ]
  ;

  ipatt:
    [ [ "{"; id = identref; ":="; p = patt; "}" -> (Some id, p)
      | p = patt -> (None, p)
      ] ]
  ;
    
  patt:
    [ [ id = smart_global -> !@loc, PEApp ((!@loc,id), [])
      | "_" -> !@loc, PEWildcard
      | "("; p = lpatt; ")" -> p
      | "?("; c = Constr.lconstr; ")" -> !@loc, PEInac c
      | p = pattern LEVEL "0" -> !@loc, PEPat p
    ] ]
  ;

  pat_head:
    [ [ id=smart_global -> (!@loc, id) 
    ] ]
  ;

  lpatt:
    [ [ head = pat_head; pats = LIST0 patt -> !@loc, PEApp (head, pats)
      | p = patt -> p
    ] ]
  ;

  refine:
    [ [ cs = LIST1 Constr.lconstr SEP "," ->
          let rec build_refine acc = function
            | [] -> assert false
            | [c] -> fun e -> acc (Refine (c, e))
            | c :: cs ->
                let acc = fun e ->
                  acc (Refine (c, [(None, RefinePats [!@loc, PEWildcard], e)])) in
                build_refine acc cs
          in build_refine (fun e -> e) cs
    ] ]
  ;
  where_clause:
    [ [ id = lident; l = binders2; ":"; t = Constr.lconstr;
        ":="; eqs = sub_equations -> ((id, l, t), eqs) ] ]
  ;
  where:
    [ [ "where"; l = LIST1 where_clause -> l
      | -> []
    ] ]
  ;
  rhs:
    [ [ ":=!"; id = identref -> Empty id
      | [":="|"=>"]; c = Constr.lconstr; w = where -> Program (c, w)
      | ["with"|"<="]; ref = refine; [":="|"=>"]; e = sub_equations -> ref e
      | "<-"; "(" ; t = Tactic.tactic; ")"; e = sub_equations -> By (Inl t, e)
      | "by"; IDENT "rec"; c = constr; rel = OPT constr; id = OPT identref;
        [":="|"=>"]; e = deppat_equations -> Rec (c, rel, id, e)
    ] ]
  ;

  sub_equations:
    [ [ "{"; l = deppat_equations; "}" -> l 
      | l = deppat_equations -> l
    ] ]
  ;

  equations:
  [ [ l = LIST1 where_clause -> l ] ]
  ;
  END

VERNAC COMMAND EXTEND Define_equations CLASSIFIED AS SIDEFF
| [ "Equations" equation_options(opt) equations(eqns)
    (* decl_notation(nt) *) ] ->
    [ Equations.equations opt eqns [] ]
      END

(* TACTIC EXTEND block_goal *)
(* [ "block_goal" ] -> [ of82 ( *)
(*   (fun gl -> *)
(*     let block = Lazy.force coq_block in *)
(*     let concl = pf_concl gl in *)
(*     let ty = pf_type_of gl concl in *)
(*     let evd = project gl in *)
(*     let newconcl = mkApp (block, [|ty; concl|]) in *)
(*     let evd, _ty = Typing.e_type_of (pf_env gl) evd newconcl in *)
(*       (\* msg_info (str "After e_type_of: " ++ pr_evar_map None evd); *\) *)
(*       tclTHEN (tclEVARS evd) *)
(* 	(convert_concl newconcl DEFAULTcast) gl)) ] *)
(* END *)
  
(* TACTIC EXTEND pattern_call *)
(* [ "pattern_call" constr(c) ] -> [ fun gl -> *)
(*   match kind_of_term c with *)
(*   | App (f, [| arg |]) -> *)
(*       let concl = pf_concl gl in *)
(*       let replcall = replace_term c (mkRel 1) concl in *)
(*       let replarg = replace_term arg (mkRel 2) replcall in *)
(*       let argty = pf_type_of gl arg and cty = pf_type_of gl c in *)
(*       let rels = [(Name (id_of_string "call"), None, replace_term arg (mkRel 1) cty); *)
(* 		  (Name (id_of_string "arg"), None, argty)] in *)
(*       let newconcl = mkApp (it_mkLambda_or_LetIn replarg rels, [| arg ; c |]) in *)
(* 	convert_concl newconcl DEFAULTcast gl  *)
(*   | _ -> tclFAIL 0 (str "Not a recognizable call") gl ] *)
(* END *)

(* Dependent elimination using Equations. *)

let pr_elim_patterns _ _ _ l = mt ()

ARGUMENT EXTEND elim_patterns
PRINTED BY pr_elim_patterns
  | [ deppat_elim(l) ] -> [ l ]
END

TACTIC EXTEND dependent_elimination
| ["dependent" "elimination" ident(id) ] -> [ Depelim.dependent_elim_tac id ]
| ["dependent" "elimination" ident(id) "as" elim_patterns(l) ] ->
    [ Depelim.dependent_elim_tac ~patterns:l id ]
END

(* Subterm *)


TACTIC EXTEND is_secvar
| [ "is_secvar" constr(x) ] ->
  [ match kind_of_term x with
    | Var id when Termops.is_section_variable id -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclFAIL 0 (str "Not a section variable or hypothesis") ]
END

open Proofview.Goal

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
         let argoccs = Array.map_to_list (fun _ -> None) (snd ev) in
         let sigma, b = Evarconv.second_order_matching ts env sigma ev argoccs concl in
         if not b then
           error "Second-order matching failed"
         else Proofview.Unsafe.tclEVARS sigma <*>
                Refine.refine ~unsafe:true { Sigma.run = fun sigma -> Sigma.here c sigma }
      | _, _ -> error "Couldn't find a second-order pattern to match"
    in aux env concl ty }

TACTIC EXTEND refine_ho
| [ "refine_ho" open_constr(c) ] ->
   [ refine_ho c ]
END

TACTIC EXTEND eqns_specialize_eqs
| [ "eqns_specialize_eqs" ident(i) ] -> [
    Proofview.V82.tactic (Depelim.specialize_eqs i)
  ]
END

TACTIC EXTEND move_after_deps
| [ "move_after_deps" ident(i) constr(c) ] ->
 [ Equations_common.move_after_deps i c ]
END

(** Deriving *)

VERNAC COMMAND EXTEND Derive CLASSIFIED AS SIDEFF
| [ "Derive" ne_ident_list(ds) "for" global_list(c) ] -> [
    Derive.derive (List.map Id.to_string ds)
                  (List.map (fun x -> Libnames.loc_of_reference x, Smartlocate.global_with_alias x) c)
  ]
END


(* Simplify *)

type simplification_rules_argtype = Simplify.simplification_rules Genarg.uniform_genarg_type

let wit_g_simplification_rules : simplification_rules_argtype =
  Genarg.create_arg "g_simplification_rules"

let pr_raw_g_simplification_rules _ _ _ = Simplify.pr_simplification_rules
let pr_glob_g_simplification_rules _ _ _ = Simplify.pr_simplification_rules
let pr_g_simplification_rules _ _ _ = Simplify.pr_simplification_rules

let g_simplification_rules : Simplify.simplification_rules Gram.entry =
  Pcoq.create_generic_entry Pcoq.utactic "g_simplification_rules"
    (Genarg.rawwit wit_g_simplification_rules)

let _ = Pptactic.declare_extra_genarg_pprule wit_g_simplification_rules
  pr_raw_g_simplification_rules pr_glob_g_simplification_rules pr_g_simplification_rules

GEXTEND Gram
  GLOBAL: g_simplification_rules;

  g_simplification_rules:
    [ [ l = LIST1 simplification_rule_located -> l ] ]
  ;

  simplification_rule_located:
    [ [ r = simplification_rule -> (!@loc, r) ] ]
  ;

  simplification_rule:
    [ [ step = simplification_step -> Simplify.Step step
      | "?" -> Simplify.Infer_one
      | "<->" -> Simplify.Infer_direction
      | "*" -> Simplify.Infer_many
    ] ];

  simplification_step :
    [ [ "-" -> Simplify.Deletion false
      | "-!" -> Simplify.Deletion true
      | "$" -> Simplify.NoConfusion []
      | "$"; "{"; rules = g_simplification_rules; "}" ->
          Simplify.NoConfusion rules
      | dir = direction -> Simplify.Solution dir
    ] ];

  direction:
    [ [ "->" -> Simplify.Left
      | "<-" -> Simplify.Right
    ] ];
END

(* We need these alias due to the limitations of parsing macros. *)
type simplification_rules = Simplify.simplification_rules
let pr_simplification_rules _ _ _ = Simplify.pr_simplification_rules

ARGUMENT EXTEND simplification_rules
PRINTED BY pr_simplification_rules
  | [ g_simplification_rules(l) ] -> [ l ]
END

TACTIC EXTEND simplify
| [ "simplify" simplification_rules(l) ] ->
  [ Simplify.simplify_tac l ]
| [ "simplify" ] ->
  [ Simplify.simplify_tac [] ]
END
