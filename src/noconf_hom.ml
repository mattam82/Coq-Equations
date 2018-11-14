(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Nameops
open Constr
open Declarations
open Globnames
open Vars
open Covering
open Equations_common
open EConstr
open Vars

let name_context env sigma ctx =
  let avoid, ctx =
    List.fold_right (fun decl (avoid, acc) ->
      let (n, b, t) = to_tuple decl in
      match n with
      | Name id -> let id' = Namegen.next_ident_away id avoid in
        let avoid = Id.Set.add id' avoid in
        (avoid, make_def (Name id') b t :: acc)
      | Anonymous ->
        let id' = Namegen.id_of_name_using_hdchar
            (push_rel_context acc env) sigma t Anonymous in
        let avoid = Id.Set.add id' avoid in
        (avoid, make_def (Name id') b t :: acc))
      ctx (Id.Set.empty, [])
  in ctx

let occur_rigidly sigma i concl =
  let rec aux concl =
    match kind sigma concl with
    | App (f, cl) ->
      if isConstruct sigma f then
        Array.exists aux cl
      else false
    | Rel k -> Int.equal k i
    | _ -> false
  in
  let hd, args = decompose_appvect sigma concl in
  Array.exists aux args

let get_forced_positions sigma args concl =
  let is_forced i acc args =
    if occur_rigidly sigma i concl then true :: acc
    else false :: acc
  in
  List.rev (List.fold_left_i is_forced 1 [] args)

let derive_no_confusion_hom env sigma ~polymorphic (ind,u as indu) =
  let mindb, oneind = Global.lookup_inductive ind in
  let pi = (fst indu, EConstr.EInstance.kind sigma (snd indu)) in
  let ctx = subst_instance_context (snd pi) oneind.mind_arity_ctxt in
  let ctx = List.map of_rel_decl ctx in
  let ctx = smash_rel_context sigma ctx in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = Array.chop params argsvect in
  let argty, x, ctx, argsctx =
    mkApp (mkIndU indu, argsvect), mkRel 1, ctx, []
  in
  let sigma, tru = get_fresh sigma logic_top in
  let sigma, fls = get_fresh sigma logic_bot in
  let ctx = name_context env sigma ctx in
  let xid = Id.of_string "x" and yid = Id.of_string "y" in
  let xdecl = of_tuple (Name xid, None, argty) in
  let binders = xdecl :: ctx in
  let ydecl = of_tuple (Name yid, None, lift 1 argty) in
  let fullbinders = ydecl :: binders in
  let sigma, s = Evd.fresh_sort_in_family sigma (Lazy.force logic_sort) in
  let s = mkSort s in
  let _arity = it_mkProd_or_LetIn s fullbinders in
  (* let env = push_rel_context binders env in *)
  let paramsvect = Context.Rel.to_extended_vect mkRel 0 ctx in
  let _pack_ind_with_parlift n = lift n argty in
  let _ind_with_parlift n =
    mkApp (mkIndU indu, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let _lenindices = List.length argsctx in
  let ctxmap = id_subst fullbinders in
  let constructors = Inductiveops.arities_of_constructors env pi in
  let sigma, sigT = get_fresh sigma coq_sigma in
  let sigma, sigI = get_fresh sigma coq_sigmaI in
  let sigma, eqT = get_fresh sigma logic_eq_type in
  let parampats =
    List.rev_map (fun decl ->
        Loc.tag (Syntax.PUVar (Name.get_id (get_name decl), true))) ctx
  in
  let mk_clause i ty =
    let ty = EConstr.of_constr ty in
    let paramsctx, concl = decompose_prod_n_assum sigma params ty in
    let _, ctxpars = List.chop args ctx in
    let ctxvars = List.map (fun decl -> mkVar (Name.get_id (get_name decl))) ctxpars in
    let args, concl = decompose_prod_assum sigma (Vars.substnl ctxvars 0 concl) in
    let forced = get_forced_positions sigma args concl in
    let loc = None in
    let fn (avoid, acc) decl forced =
      let id = match Context.Rel.Declaration.get_name decl with
        | Name na -> na
        | Anonymous -> Id.of_string "wildcard"
      in
      let name = Namegen.next_ident_away (add_suffix id "0") avoid in
      let avoid = Id.Set.add name avoid in
      let name' = Namegen.next_ident_away (add_suffix id "1") avoid in
      let acc =
        if forced then
          let acc' = List.fold_left_i
              (fun i acc (na,na',decl) -> (na, na', Vars.substnl [mkVar name'] i decl) :: acc) 0 [] acc in
          List.rev acc'
        else ((name, name', get_type decl) :: acc) in
      (avoid, acc), (Syntax.PUVar (name, true), Syntax.PUVar (name', true))
    in
    let (avoid, eqs), user_pats = List.fold_left2_map fn (Id.Set.empty, []) args forced in
    let patl, patr = List.split user_pats in
    let cstr ps = Syntax.PUCstr ((ind, succ i), params, List.rev_map (fun p -> Loc.tag p) ps) in
    let lhs = parampats @ [Loc.tag (cstr patl); Loc.tag (cstr patr)] in
    let rhs =
      match List.rev eqs with
      | [] -> tru
      | (name, name', ty) :: eqs ->
        let ty, lhs, rhs =
          let get_type (na, na', ty) (restty, restl, restr) =
            let codom = mkLambda (Name na, ty, restty) in
            mkApp (sigT, [| ty; codom |]),
            mkApp (sigI, [| ty; codom; mkVar na; restl |]),
            mkApp (sigI, [| ty; codom; mkVar na'; restr |])
          in
          List.fold_right get_type eqs (ty, mkVar name, mkVar name')
        in mkApp (eqT, [| ty; lhs; rhs |])
    in
    (loc, lhs, Syntax.Program (Syntax.Constr rhs, []))
  in
  let clauses = Array.mapi mk_clause constructors in
  let indid = Nametab.basename_of_global (IndRef ind) in
  let id = add_prefix "NoConfusionHom_" indid in
  let evd = ref sigma in
  let splitting = Covering.covering env evd
      (id, false, Names.Id.Map.empty)
      (Array.to_list clauses) [] ctxmap s in
  let hook split fn terminfo ustate =
    let proginfo =
      Splitting.{ program_id = id;
        program_sign = fullbinders;
        program_arity = s;
        program_oarity = s;
        program_rec_annot = None;
        program_rec = None;
        program_impls = [] }
    in
    let compiled_info = Splitting.{ program_cst = (match terminfo.term_id with ConstRef c -> c | _ -> assert false);
                          program_split = split;
                          program_split_info = terminfo } in
    let flags = { polymorphic; with_eqns = true; with_ind = true } in
    let fixprots = [s] in
    Equations.define_principles flags fixprots [proginfo, compiled_info]
 in
  Splitting.define_tree None [] polymorphic [] (Evar_kinds.Define false) evd env
                (id, fullbinders, s)
                None splitting hook


  (* let _, ce = make_definition ~poly:polymorphic !evd ~types:arity app in
   * let id = add_prefix "NoConfusion_" indid
   * and noid = add_prefix "noConfusion_" indid
   * and packid = add_prefix "NoConfusionPackage_" indid in
   * let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in
   * let env = Global.env () in
   * let evd = ref (Evd.from_env env) in
   * let tc = Typeclasses.class_info (Lazy.force coq_noconfusion_class) in
   * let noconf = e_new_global evd (ConstRef cstNoConf) in
   * let noconfcl = e_new_global evd tc.Typeclasses.cl_impl in
   * let inst, u = destInd !evd noconfcl in
   * let noconfterm = mkApp (noconf, paramsvect) in
   * let ctx, argty =
   *   let ty = Retyping.get_type_of env !evd noconf in
   *   let ctx, ty = EConstr.decompose_prod_n_assum !evd params ty in
   *   match kind !evd ty with
   *   | Prod (_, b, _) -> ctx, b
   *   | _ -> assert false
   * in
   * let b, ty =
   *   Equations_common.instance_constructor !evd (tc,u) [argty; noconfterm]
   * in
   * let env = push_rel_context ctx (Global.env ()) in
   * let rec term c ty =
   *   match kind !evd ty with
   *   | Prod (na, t, ty) ->
   *      let arg = Equations_common.evd_comb1 (Evarutil.new_evar env) evd t in
   *      term (mkApp (c, [|arg|])) (subst1 arg ty)
   *   | _ -> c, ty
   * in
   * let cty = Retyping.get_type_of env !evd (Option.get b) in
   * let term, ty = term (Option.get b) cty in
   * let term = it_mkLambda_or_LetIn term ctx in
   * let ty = it_mkProd_or_LetIn ty ctx in
   * let _ = Equations_common.evd_comb1 (Typing.type_of env) evd term in
   * let hook _ectx _evars vis gr =
   *   Typeclasses.add_instance
   *     (Typeclasses.new_instance tc empty_hint_info true gr)
   * in
   * let kind = (Global, polymorphic, Definition) in
   * let oblinfo, _, term, ty = Obligations.eterm_obligations env noid !evd 0
   *     (to_constr ~abort_on_undefined_evars:false !evd term)
   *     (to_constr !evd ty) in
   *   ignore(Obligations.add_definition ~hook:(Obligations.mk_univ_hook hook) packid
   *            ~kind ~term ty ~tactic:(noconf_tac ())
   *             (Evd.evar_universe_context !evd) oblinfo) *)

let () =
  Ederive.(register_derive
             { derive_name = "NoConfusionHom";
               derive_fn = make_derive_ind derive_no_confusion_hom })
