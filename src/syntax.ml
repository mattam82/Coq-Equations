(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Printer
open Ppconstr
open Util
open Names
open Constr
open Globnames
open Pp
open Glob_term
open List
open Libnames
open Constrexpr_ops
open Constrexpr
open Evar_kinds
open Equations_common
open Constrintern
open Ltac_plugin

type 'a with_loc = Loc.t * 'a
type identifier = Names.Id.t
   
type generated = bool
(** User-level patterns *)
type user_pat =
    PUVar of identifier * generated
  | PUCstr of constructor * int * user_pats
  | PUInac of Constrexpr.constr_expr
and user_pat_loc = (user_pat, [ `any ]) DAst.t
and user_pats = user_pat_loc list

(** AST *)

type pat_expr =
  | PEApp of qualid Constrexpr.or_by_notation with_loc * pat_expr with_loc list
  | PEWildcard
  | PEInac of constr_expr

type user_pat_expr = pat_expr with_loc

type 'a input_pats =
  | SignPats of 'a
  | RefinePats of 'a list

type rec_annotation =
  | Nested
  | Mutual

type user_rec_annot = rec_annotation option

type rec_arg = int * Id.t with_loc option
    
type rec_annot =
  | MutualOn of rec_arg
  | NestedOn of rec_arg option

type program_body =
  | ConstrExpr of Constrexpr.constr_expr
  | Constr of EConstr.constr (* We interpret a constr by substituting
                                [Var names] of the lhs bound variables
                                with the proper de Bruijn indices *)

type lhs = user_pats

type 'a rhs =
  | Program of program_body * 'a where_clause list
  | Empty of identifier with_loc
  | Rec of constr_expr * constr_expr option *
             identifier with_loc option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list

and pre_prototype =
  identifier with_loc * user_rec_annot * Constrexpr.local_binder_expr list * Constrexpr.constr_expr *
  (Id.t with_loc, Constrexpr.constr_expr * Constrexpr.constr_expr option) by_annot option

and ('a, 'b) by_annot =
  | Structural of 'a
  | WellFounded of 'b

and 'a where_clause = pre_prototype * 'a list

type program = (signature * clause list) list
and signature = identifier * rel_context * constr (* f : Π Δ. τ *)
and clause = Loc.t option * lhs * clause rhs (* lhs rhs *)

type pre_equation_lhs =
  | RawLhs of Constrexpr.constr_expr input_pats
  | GlobLhs of Loc.t option * lhs

type pre_equation =
  pre_equation_lhs * pre_equation rhs

type pre_clause = Loc.t option * lhs * pre_equation rhs

type pre_equations = pre_equation where_clause list

let rec pr_user_loc_pat env ?loc pat =
  match pat with
  | PUVar (i, gen) -> Id.print i ++ if gen then str "#" else mt ()
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
	if not (List.is_empty f) then str "(" ++ pc ++ spc () ++ pr_user_pats env f ++ str ")"
	else pc
  | PUInac c -> str "?(" ++ pr_constr_expr c ++ str ")"

and pr_user_pat env = DAst.with_loc_val (pr_user_loc_pat env)

and pr_user_pats env pats =
  prlist_with_sep spc (pr_user_pat env) pats

let pr_lhs = pr_user_pats

let pplhs lhs = pp (pr_lhs (Global.env ()) lhs)

let rec pr_rhs env = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Rec (t, rel, id, s) -> 
     spc () ++ str "=>" ++ spc () ++ str"rec " ++ pr_constr_expr t ++ spc () ++
       pr_opt (fun (_, id) -> Id.print id) id ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++
                            (match rhs with
                             | ConstrExpr rhs -> pr_constr_expr rhs
                             | Constr c -> str"<constr>") ++
                            spc () ++ pr_wheres env where
  | Refine (rhs, s) -> spc () ++ str "<=" ++ spc () ++ pr_constr_expr rhs ++ 
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")

and pr_wheres env l =
  if List.is_empty l then mt() else
  str"where" ++ spc () ++ prlist_with_sep fnl (pr_where env) l
and pr_where env (sign, eqns) =
  pr_proto sign ++ str "{" ++ pr_clauses env eqns ++ str "}"
and pr_proto ((_,id), _, l, t, ann) =
  Id.print id ++ pr_binders l ++ str" : " ++ pr_constr_expr t ++
  (match ann with
     None -> mt ()
   | Some (WellFounded (t, rel)) -> str"by rec " ++ pr_constr_expr t ++ pr_opt pr_constr_expr rel
   | Some (Structural id) -> str"by struct " ++ pr_id (snd id))

and pr_clause env (loc, lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let pr_user_lhs env lhs =
  match lhs with
  | SignPats x -> pr_constr_expr x
  | RefinePats l -> prlist_with_sep (fun () -> str "|") pr_constr_expr l

let rec pr_prerhs env = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ Id.print var
  | Rec (t, rel, id, s) ->
     spc () ++ str "=>" ++ spc () ++ str"rec " ++ pr_constr_expr t ++ spc () ++
       pr_opt (fun (_, id) -> Id.print id) id ++ spc () ++
      hov 1 (str "{" ++ pr_user_clauses env s ++ str "}")
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++
                            (match rhs with
                             | ConstrExpr rhs -> pr_constr_expr rhs
                             | Constr c -> str"<constr>") ++
                            spc () ++ pr_prewheres env where
  | Refine (rhs, s) -> spc () ++ str "<=" ++ spc () ++ pr_constr_expr rhs ++
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_user_clauses env s ++ str "}")
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic tac
      ++ spc () ++ hov 1 (str "{" ++ pr_user_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_user_clauses env s ++ str "}")

and pr_pre_user_lhs env = function
  | RawLhs lhs -> pr_user_lhs env lhs
  | GlobLhs (loc, lhs) -> pr_lhs env lhs

and pr_user_clause env (lhs, rhs) =
  pr_pre_user_lhs env lhs ++ pr_prerhs env rhs

and pr_user_clauses env =
  prlist_with_sep fnl (pr_user_clause env)

and pr_prewheres env l =
  if List.is_empty l then mt() else
  str"where" ++ spc () ++ prlist_with_sep fnl (pr_prewhere env) l
and pr_prewhere env (sign, eqns) =
  pr_proto sign ++ str "{" ++ pr_user_clauses env eqns ++ str "}"

let pr_preclause env (loc, lhs, rhs) =
  pr_lhs env lhs ++ pr_prerhs env rhs

let pr_preclauses env =
  prlist_with_sep fnl (pr_preclause env)

let ppclause clause =
  pp(pr_clause (Global.env ()) clause)

let wit_equations_list : pre_equation list Genarg.uniform_genarg_type =
  Genarg.create_arg "equations_list"

let next_ident_away s ids =
  let n' = Namegen.next_ident_away s !ids in
    ids := Id.Set.add n' !ids; n'

type equation_option = | OInd of bool | ORec of Id.t with_loc option
                       | OComp of bool | OEquations of bool
    
type equation_user_option = equation_option

type equation_options = equation_option list

let pr_r_equation_user_option _prc _prlc _prt l =
  mt ()

let pr_equation_options  _prc _prlc _prt l =
  mt ()

type rec_type = 
  | Guarded of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of logical_rec

and logical_rec =
  | LogicalDirect of Id.t with_loc
  | LogicalProj of rec_info

and rec_info = {
  comp_app : Constr.t;
  comp_proj : Constant.t;
  comp_recarg : int;
}

let is_structural = function Some (Guarded _) -> true | _ -> false

let is_rec_call sigma r f =
  match r with
  | LogicalProj r -> Equations_common.is_global sigma (ConstRef r.comp_proj) f
  | LogicalDirect (loc, id) -> 
    match EConstr.kind sigma f with
    | Var id' -> Id.equal id id'
    | Const (c, _) ->
      let id' = Label.to_id (Constant.label c) in
      Id.equal id id'
    | _ -> false

let default_loc = Loc.make_loc (0, 0)
         
let is_inaccessible_qualid qid =
  let id = qualid_basename qid in
  Id.equal id (Id.of_string "inaccessible_pattern")

let free_vars_of_constr_expr fid c =
  let rec aux bdvars l = function
    | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
      let id = qualid_basename qid in
      if Id.List.mem id bdvars then l
      else if Option.cata (Id.equal id) false fid then l
      else
        (try
           match Nametab.locate_extended (Libnames.qualid_of_ident id) with
           | TrueGlobal gr ->
             if not (isConstructRef gr) then Id.Set.add id l
             else l
           | SynDef _ -> l
         with Not_found -> Id.Set.add id l)
    | { CAst.v = CApp ((_, { CAst.v = CRef (qid, _) }), _) }
      when is_inaccessible_qualid qid -> l
    | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] Id.Set.empty c

let ids_of_pats id pats =
  fold_left (fun ids p -> Id.Set.union ids (free_vars_of_constr_expr id p))
    Id.Set.empty pats

type wf_rec_info =
  EConstr.constr * EConstr.constr option * logical_rec

type program_rec_info =
  (rec_annot, wf_rec_info) by_annot

type program_info = {
  program_loc : Loc.t;
  program_id : Id.t;
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec : program_rec_info option;
  program_impls : Impargs.manual_explicitation list;
}

let chole c loc =
  (* let tac = Genarg.in_gen (Genarg.rawwit Constrarg.wit_tactic) (solve_rec_tac_expr ()) in *)
  let kn = Lib.make_kn c in
  let cst = Names.Constant.make kn kn in
  CAst.make ~loc
  (CHole (Some (ImplicitArg (ConstRef cst, (0,None), false)), Namegen.IntroAnonymous,None)), None

let check_linearity pats =
  let rec aux ids pats = 
    List.fold_left (fun ids pat ->
      DAst.with_loc_val (fun ?loc pat ->
      match pat with
      | PUVar (n, _) ->
	if Id.Set.mem n ids then
	  CErrors.user_err ?loc ~hdr:"ids_of_pats"
	    (str "Non-linear occurrence of variable in patterns")
	else Id.Set.add n ids
      | PUInac _ -> ids
      | PUCstr (_, _, pats) -> aux ids pats) pat)
      ids pats
  in ignore (aux Id.Set.empty pats)

let pattern_of_glob_constr env avoid gc =
  let rec constructor ?loc c l =
    let ind, _ = c in
    let nparams = Inductiveops.inductive_nparams ind in
    let nargs = Inductiveops.constructor_nrealargs c in
    let l =
      if List.length l < nargs then
        user_err_loc (loc, "pattern_of_glob_constr", str "Constructor is applied to too few arguments")
      else
        if List.length l = nparams + nargs then
          List.skipn nparams l
        else if List.length l = nargs then l
        else
          user_err_loc (loc, "pattern_of_glob_constr", str "Constructor is applied to too many arguments");
    in
    Dumpglob.add_glob ?loc (ConstructRef c);
    PUCstr (c, nparams, List.map (DAst.map_with_loc aux) l)
  and aux ?loc = function
    | GVar id -> PUVar (id, false)
    | GHole (_,_,_) ->
      let n = next_ident_away (Id.of_string "wildcard") avoid in
      avoid := Id.Set.add n !avoid; PUVar (n, true)
    | GRef (ConstructRef cstr,_) -> constructor ?loc cstr []
    | GApp (c, l) ->
      begin match DAst.get c with
        | GRef (ConstructRef cstr,_) -> constructor ?loc cstr l
        | GRef (ConstRef _ as c, _) when GlobRef.equal c (Lazy.force coq_inacc) ->
          let inacc = List.hd (List.tl l) in
          PUInac (Constrextern.extern_glob_constr !avoid inacc)
        | _ -> user_err_loc (loc, "pattern_of_glob_constr", str "Cannot interpret " ++ pr_glob_constr_env env c ++ str " as a constructor")
      end
  (* | GLetIn (Name id as na',b,None,e) when is_gvar id e && na = Anonymous ->
   *    (\* A canonical encoding of aliases *\)
   *    DAst.get (cases_pattern_of_glob_constr na' b) *)
    | _ -> user_err_loc (loc, "pattern_of_glob_constr", str ("Cannot interpret globalized term as a pattern"))
  in DAst.map_with_loc aux gc

let program_type p = EConstr.it_mkProd_or_LetIn p.program_arity p.program_sign

let interp_pat env ?(avoid = ref Id.Set.empty) p pat =
  let sigma = Evd.from_env env in
  let vars = (Id.Set.elements !avoid) (* (ids_of_pats [p])) *) in
  (* let () = Feedback.msg_debug (str"Variables " ++ prlist_with_sep spc pr_id vars) in *)
  let tys = List.map (fun _ -> EConstr.mkProp) vars in
  let impls = List.map (fun _ -> []) vars in
  let vars, tys, impls =
    match p with
    | Some p ->
      let ty = program_type p in
      (p.program_id :: vars, ty :: tys, p.program_impls :: impls)
    | None -> (vars, tys, impls)
  in
  (* let () = Feedback.msg_debug (str"Internalizing " ++ pr_constr_expr p) in *)
  let ienv = try compute_internalization_env env sigma Recursive vars tys impls with Not_found ->
    anomaly (str"Building internalization environment")
  in
  let nctx =
    List.map (fun id -> Context.Named.Declaration.LocalAssum (id, Constr.mkProp)) vars
  in
  let env = Environ.push_named_context nctx env in
  let gc =
    try Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~impls:ienv env sigma pat
    with Not_found -> anomaly (str"Internalizing pattern")
  in
  try
    match p with
    | Some { program_id = id } ->
      DAst.with_loc_val (fun ?loc g ->
          match g with
          | GApp (fn, args) ->
            DAst.with_loc_val (fun ?loc gh ->
                match gh with
                | GVar fid when Id.equal fid id ->
                  let args = List.map (pattern_of_glob_constr env avoid) args in
                  args
                | _ ->
                  user_err_loc (loc, "interp_pats",
                                str "Expecting a pattern for " ++ Id.print id))
              fn
          | _ ->
            user_err_loc (loc, "interp_pats",
                          str "Expecting a pattern for " ++ Id.print id))
        gc
    | None -> [pattern_of_glob_constr env avoid gc]
  with Not_found -> anomaly (str"While translating pattern to glob constr")

let interp_eqn env is_rec p curpats eqn =
  let avoid = ref Id.Set.empty in
  let whereid = ref (Nameops.add_suffix p.program_id "abs_where") in
  let interp_pat = interp_pat env ~avoid in
  let rec aux (pat, rhs) = (pat, interp_rhs rhs)
  and interp_rhs = function
    | Refine (c, eqs) ->
       let wheres, c = CAst.with_loc_val interp_constr_expr c in
       if not (List.is_empty wheres) then
         user_err_loc (Constrexpr_ops.constr_loc c, "interp_eqns", str"Pattern-matching lambdas not allowed in refine");
       Refine (c, map aux eqs)
    | Program (c, w) ->
       let w = interp_wheres avoid w in
       let w', c =
         match c with
         | ConstrExpr c ->
            let wheres, c = CAst.with_loc_val interp_constr_expr c in
            wheres, ConstrExpr c
         | Constr c -> [], Constr c
       in
       Program (c, List.append w' w)
    | Empty i -> Empty i
    | Rec (fni, r, id, s) -> Rec (fni, r, id, map aux s)
    | By (x, s) -> By (x, map aux s)
  and interp_wheres avoid w =
    let interp_where (((loc,id),nested,b,t,reca) as p,eqns) =
      Dumpglob.dump_reference ~loc "<>" (Id.to_string id) "def";
      p, map aux eqns
    in List.map interp_where w
  and interp_constr_expr ?(loc=default_loc) c =
    let wheres = ref [] in
    let rec aux' ids ?(loc=default_loc) c =
      match c with
      | CApp ((None, { CAst.v = CRef (qid', ie) }), args)
           when qualid_is_ident qid' && Id.equal (qualid_basename qid') p.program_id ->
         let id' = qualid_basename qid' in
         (match p.program_rec with
          | None | Some (Structural _) -> CAst.make ~loc c
          | Some (WellFounded (_, _, r)) ->
            let args =
              List.map (fun (c, expl) -> CAst.with_loc_val (aux' ids) c, expl) args in
            let c = CApp ((None, CAst.(make ~loc (CRef (qid', ie)))), args) in
            let arg = CAst.make ~loc (CApp ((None, CAst.make ~loc c), [chole id' loc])) in
            (match r with
             | LogicalDirect _ -> arg
             | LogicalProj r ->
               let arg = [arg, None] in
               let qidproj = Nametab.shortest_qualid_of_global ?loc:qid'.CAst.loc Id.Set.empty (ConstRef r.comp_proj) in
               CAst.make ~loc (CApp ((None, CAst.make ?loc:qid'.CAst.loc (CRef (qidproj, None))),
                                     args @ arg))))
      | CHole (k, i, Some eqns) when Genarg.has_type eqns (Genarg.rawwit wit_equations_list) ->
         let eqns = Genarg.out_gen (Genarg.rawwit wit_equations_list) eqns in
         let id = !whereid in
         let () = avoid := Id.Set.add id !avoid in
         let eqns = List.map aux eqns in
         let () =
           wheres := (((loc, id), None, [], CAst.make ~loc (CHole (k, i, None)), None), eqns) :: !wheres;
           whereid := Nameops.increment_subscript id;
         in Constrexpr_ops.mkIdentC id
      | _ -> map_constr_expr_with_binders Id.Set.add
             (fun avoid -> CAst.with_loc_val (aux' avoid)) ids (CAst.make ~loc c)
    in
    let c' = aux' !avoid ~loc c in
    !wheres, c'
  in
  let interp_eqn curpats (pat, rhs) =
    let loc, pats =
      match pat with
      | RawLhs (SignPats pat) ->
        avoid := Id.Set.union !avoid (ids_of_pats (Some p.program_id) [pat]);
        let loc = Constrexpr_ops.constr_loc pat in
        loc, interp_pat (Some p) pat
      | RawLhs (RefinePats pats) ->
        avoid := Id.Set.union !avoid (ids_of_pats None pats);
        let loc = Constrexpr_ops.constr_loc (List.hd pats) in
        let pats = List.map (interp_pat None) pats in
        let pats = List.map (fun x -> List.hd x) pats in
        loc, curpats @ pats
      | GlobLhs (loc, pats) -> loc, pats
    in
    let () = check_linearity pats in
    (loc, pats, interp_rhs rhs)
  in interp_eqn curpats eqn

let is_recursive i : pre_equations -> bool option = fun eqs ->
  let rec occur_eqn (_, rhs) =
    match rhs with
    | Program (c,w) ->
      (match c with
      | ConstrExpr c ->
        if occur_var_constr_expr i c then Some false else occurs w
      | Constr _ -> occurs w)
    | Refine (c, eqs) ->
       if occur_var_constr_expr i c then Some false
       else occur_eqns eqs
    | Rec _ -> Some true
    | _ -> None
  and occur_eqns eqs =
    let occurs = List.map occur_eqn eqs in
    if for_all Option.is_empty occurs then None
    else if exists (function Some true -> true | _ -> false) occurs then Some true
    else Some false
  and occurs eqs =
    let occurs = List.map (fun (_,eqs) -> occur_eqns eqs) eqs in
      if for_all Option.is_empty occurs then None
      else if exists (function Some true -> true | _ -> false) occurs then Some true
      else Some false
  in occurs eqs
