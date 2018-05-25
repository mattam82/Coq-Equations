(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)


(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "equations_plugin"

open Constr
open Names
open Pp
open Refiner
open Constrexpr
open Stdarg
open Equations_common
open EConstr
open Ltac_plugin
open Pltac

let of82 = Proofview.V82.tactic

TACTIC EXTEND decompose_app
[ "decompose_app" ident(h) ident(h') constr(c) ] -> [ Extra_tactics.decompose_app h h' c ]
END

TACTIC EXTEND autounfold_ref
| [ "autounfold_ref" reference(myref) ] -> [ Extra_tactics.autounfold_ref myref ]
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

open Proofview.Goal

TACTIC EXTEND get_signature_pack
[ "get_signature_pack" hyp(id) ident(id') ] ->
     [ Sigma_types.Tactics.get_signature_pack id id' ]
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
| [ "pattern" "sigma" hyp(id) ] -> [ Sigma_types.Tactics.pattern_sigma id ]
END

TACTIC EXTEND curry
[ "curry" hyp(id) ] -> [ Sigma_types.Tactics.curry_hyp id ]
| ["curry"] -> [ Sigma_types.Tactics.curry ]
END

TACTIC EXTEND curry_hyps
[ "uncurry_hyps" ident(id) ] -> [ Sigma_types.uncurry_hyps id ]
END

TACTIC EXTEND uncurry_call
[ "uncurry_call" constr(c) ident(id) ] -> [ Sigma_types.Tactics.uncurry_call c id ]
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
[ "pattern_call" constr(c) ] -> [ Proofview.V82.tactic (Depelim.pattern_call c) ]
END

(* Noconf *)

VERNAC COMMAND EXTEND Equations_Logic CLASSIFIED AS QUERY
| [ "Equations" "Logic" sort_family(s) global(eq) global(eqr) global(eq_case) global(eq_elim)
                global(z) global(o) global(ov) global(oprod) global(opair) ] -> [
  let gr x = Lazy.from_val (Nametab.global x) in
  Equations_common.(set_logic { logic_eq_ty = gr eq;
				logic_eq_refl = gr eqr;
                                logic_eq_case = gr eq_case;
                                logic_eq_elim = gr eq_elim;
                                logic_sort = s;
				logic_zero = gr z;
				logic_one = gr o;
				logic_one_val = gr ov;
                                logic_product = gr oprod;
                                logic_pair = gr opair;
  })
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

open Tacarg
TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(destruct) tactic(tac) ] -> 
     [ of82 (Equations.solve_equations_goal (to82 (Tacinterp.tactic_of_value ist destruct))
                                            (to82 (Tacinterp.tactic_of_value ist tac))) ]
END

TACTIC EXTEND simp
| [ "simp" ne_preident_list(l) clause(c) ] -> 
    [ of82 (Principles_proofs.simp_eqns_in c l) ]
| [ "simpc" constr_list(l) clause(c) ] -> 
   [ of82 (Principles_proofs.simp_eqns_in
                        c
                        (dbs_of_constrs (List.map EConstr.Unsafe.to_constr l))) ]
END


(* let wit_r_equation_user_option : equation_user_option Genarg.uniform_genarg_type = *)
(*   Genarg.create_arg None "r_equation_user_option" *)

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

let pr_lident _ _ _ (loc, id) = Id.print id
       
ARGUMENT EXTEND lident
PRINTED BY pr_lident
| [ ident(i) ] -> [ (loc, i) ]
END


module Gram = Pcoq.Gram
module Vernac = Pvernac.Vernac_

type binders_argtype = Constrexpr.local_binder_expr list Genarg.uniform_genarg_type

let pr_raw_binders2 _ _ _ l = mt ()
let pr_glob_binders2 _ _ _ l = mt ()
let pr_binders2 _ _ _ l = mt ()

(* let wit_binders_let2 : binders_let2_argtype = *)
(*   Genarg.create_arg "binders_let2" *)

let wit_binders2 : binders_argtype =
  Genarg.create_arg "binders2"

let binders2 : local_binder_expr list Gram.entry =
  Pcoq.create_generic_entry Pcoq.uconstr "binders2" (Genarg.rawwit wit_binders2)

let binders2_val = Geninterp.register_val0 wit_binders2 None

let _ = Pptactic.declare_extra_genarg_pprule wit_binders2
  pr_raw_binders2 pr_glob_binders2 pr_binders2

type deppat_equations_argtype = Syntax.pre_equation list Genarg.uniform_genarg_type

let wit_deppat_equations : deppat_equations_argtype =
  Genarg.create_arg "deppat_equations"

let deppat_equations_val = Geninterp.register_val0 wit_deppat_equations None

let pr_raw_deppat_equations _ _ _ l = mt ()
let pr_glob_deppat_equations _ _ _ l = mt ()
let pr_deppat_equations _ _ _ l = mt ()

let deppat_equations : Syntax.pre_equation list Gram.entry =
  Pcoq.create_generic_entry Pvernac.uvernac "deppat_equations" (Genarg.rawwit wit_deppat_equations)

let _ = Pptactic.declare_extra_genarg_pprule wit_deppat_equations
  pr_raw_deppat_equations pr_glob_deppat_equations pr_deppat_equations

type deppat_elim_argtype = Syntax.user_pat_expr list Genarg.uniform_genarg_type

let wit_deppat_elim : deppat_elim_argtype =
 Genarg.create_arg "deppat_elim"

let deppat_elim_val = Geninterp.register_val0 wit_deppat_elim None

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
let val_equations = Geninterp.register_val0 wit_equations None

let pr_raw_equations _ _ _ l = mt ()
let pr_glob_equations _ _ _ l = mt ()
let pr_equations _ _ _ l = mt ()

let equations : pre_equation where_clause list Gram.entry =
  Pcoq.create_generic_entry Pvernac.uvernac "equations" (Genarg.rawwit wit_equations)

let _ = Pptactic.declare_extra_genarg_pprule wit_equations
  pr_raw_equations pr_glob_equations pr_equations

(* preidents that are not interpreted focused *)
let interp_my_preident ist s = s

let make0 ?dyn name =
  let wit = Genarg.make0 name in
  let () = Geninterp.register_val0 wit dyn in
  wit

let wit_my_preident : string Genarg.uniform_genarg_type =
  make0 ~dyn:(Geninterp.val_tag (Genarg.topwit wit_string)) "my_preident"

let def_intern ist x = (ist, x)
let def_subst _ x = x
let def_interp ist x = Ftactic.return x

let register_interp0 wit f =
  let interp ist v =
    Ftactic.bind (f ist v)
      (fun v -> Ftactic.return (Geninterp.Val.inject (Geninterp.val_tag (Genarg.topwit wit)) v))
  in
  Geninterp.register_interp0 wit interp

let declare_uniform t =
  Genintern.register_intern0 t def_intern;
  Genintern.register_subst0 t def_subst;
  register_interp0 t def_interp

let () =
  declare_uniform wit_my_preident

let my_preident : string Gram.entry =
  Pcoq.create_generic_entry Pcoq.utactic "my_preident" (Genarg.rawwit wit_my_preident)

open Util
open Pcoq
open Prim
open Constr
open Syntax

GEXTEND Gram
  GLOBAL: pattern deppat_equations deppat_elim binders2 equations lident my_preident;

  my_preident:
    [ [ id = IDENT -> id ] ]
  ;
  binders2 : 
     [ [ b = binders -> b ] ]
  ;
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  deppat_elim:
    [ [ "["; l = LIST0 lpatt SEP "|"; "]" -> l ] ]
  ;

  identloc :
   [ [ id = ident -> (!@loc, id) ] ] ;
  equation:
    [ [ id = identloc; 	pats = LIST1 ipatt; r = rhs -> (Some id, SignPats pats, r)
      | "|"; pats = LIST1 lpatt SEP "|"; r = rhs -> (None, RefinePats pats, r) 
    ] ]
  ;

  ipatt:
    [ [ "{"; id = identloc; ":="; p = patt; "}" -> (Some id, p)
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
  struct_annot:
    [ [ "("; "struct"; id = identloc; ")" -> Some id
      | -> None
    ] ]
  ;
  rec_annot:
    [ [ "where"; an = struct_annot -> Some (Nested, an)
      | "with"; an = struct_annot -> Some (Struct, an)
      | -> None
    ] ]
  ;

  where_clause:
    [ [ r = rec_annot;
        id = lident; l = binders2; ":"; t = Constr.lconstr;
        ":="; eqs = sub_equations -> ((id, r, l, t), eqs) ] ]
  ;
  where:
    [ [ "where"; l = LIST1 where_clause -> l
      | -> []
    ] ]
  ;
  rhs:
    [ [ ":=!"; id = identloc -> Empty id
      | [":="|"=>"]; c = Constr.lconstr; w = where -> Program (c, w)
      | ["with"|"<="]; ref = refine; [":="|"=>"]; e = sub_equations -> ref e
      | "<-"; "(" ; t = tactic; ")"; e = sub_equations -> By (Inl t, e)
      | "by"; IDENT "rec"; c = constr; rel = OPT constr; id = OPT identloc;
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
(*       let rels = [(Name (Id.of_string "call"), None, replace_term arg (mkRel 1) cty); *)
(* 		  (Name (Id.of_string "arg"), None, argty)] in *)
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
| ["dependent" "elimination" ident(id) ] -> [ Depelim.dependent_elim_tac (Loc.make_loc (0, 0), id) ]
| ["dependent" "elimination" ident(id) "as" elim_patterns(l) ] ->
   [ Depelim.dependent_elim_tac ~patterns:l (Loc.make_loc (0, 0), id) (* FIXME *) ]
END

(* Subterm *)


TACTIC EXTEND is_secvar
| [ "is_secvar" constr(x) ] ->
   [ enter (fun gl ->
     match kind (Proofview.Goal.sigma gl) x with
     | Var id when Termops.is_section_variable id -> Proofview.tclUNIT ()
     | _ -> Tacticals.New.tclFAIL 0 (str "Not a section variable or hypothesis")) ]
END

TACTIC EXTEND refine_ho
| [ "refine_ho" open_constr(c) ] -> [ Extra_tactics.refine_ho c ]
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

VERNAC COMMAND FUNCTIONAL EXTEND Derive CLASSIFIED AS SIDEFF
| [ "Derive" ne_ident_list(ds) "for" global_list(c) ] -> [
  fun ~atts ~st -> Ederive.derive ~poly:atts.Vernacinterp.polymorphic (List.map Id.to_string ds)
    (List.map (fun x -> x.CAst.loc, Smartlocate.global_with_alias x) c); st
  ]
END


(* Simplify *)

type simplification_rules_argtype = Simplify.simplification_rules Genarg.uniform_genarg_type

let wit_g_simplification_rules : simplification_rules_argtype =
  Genarg.create_arg "g_simplification_rules"

let val_g_simplification_rules =
  Geninterp.register_val0 wit_g_simplification_rules None

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
    [ [ r = simplification_rule -> (Some !@loc, r) ] ]
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

TACTIC EXTEND mutual_fix
[ "mfix" my_preident_list(li) int_list(l) ] -> [ Principles_proofs.mutual_fix li l ]
END
  
