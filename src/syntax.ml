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
and user_pats = user_pat located list

(** AST *)

type rec_annotation =
  | Nested
  | Struct

type user_rec_annot = (rec_annotation * Id.t with_loc option) option

type rec_arg = int * Id.t with_loc option
    
type rec_annot =
  | StructuralOn of rec_arg
  | NestedOn of rec_arg option

type program =
  (signature * clause list) list

and signature = identifier * rel_context * Constr.t
  
and clause = Loc.t * lhs * clause rhs
  
and lhs = user_pats

and 'a rhs = 
  | Program of constr_expr * 'a where_clause list
  | Empty of identifier with_loc
  | Rec of constr_expr * constr_expr option *
             identifier with_loc option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list

and prototype =
  identifier with_loc * user_rec_annot * Constrexpr.local_binder_expr list * Constrexpr.constr_expr

and 'a where_clause = prototype * 'a list

let rec pr_user_pat env (loc,pat) =
  match pat with
  | PUVar (i, gen) -> Id.print i ++ if gen then str "#" else mt ()
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
	if not (List.is_empty f) then str "(" ++ pc ++ spc () ++ pr_user_pats env f ++ str ")"
	else pc
  | PUInac c -> str "?(" ++ pr_constr_expr c ++ str ")"

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
  | Program (rhs, where) -> spc () ++ str ":=" ++ spc () ++ pr_constr_expr rhs ++
                             pr_wheres env where
  | Refine (rhs, s) -> spc () ++ str "<=" ++ spc () ++ pr_constr_expr rhs ++ 
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")

and pr_wheres env l =
  prlist_with_sep fnl (pr_where env) l
and pr_where env (sign, eqns) =
  pr_proto sign ++ pr_clauses env eqns
and pr_proto ((_,id), _, l, t) =
  Id.print id ++ pr_binders l ++ str" : " ++ pr_constr_expr t
and pr_clause env (loc, lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let ppclause clause =
  pp(pr_clause (Global.env ()) clause)

type pat_expr = 
  | PEApp of reference Misctypes.or_by_notation with_loc * pat_expr with_loc list
  | PEWildcard
  | PEInac of constr_expr
  | PEPat of cases_pattern_expr

type user_pat_expr = pat_expr with_loc

type input_pats =
  | SignPats of (Id.t with_loc option * user_pat_expr) list
  | RefinePats of user_pat_expr list

type pre_equation = 
  identifier with_loc option * input_pats * pre_equation rhs

type pre_equations = pre_equation where_clause list

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
  | Structural of (Id.t * rec_annot) list (* for mutual rec *)
  | Logical of logical_rec

and logical_rec =
  | LogicalDirect of Id.t with_loc
  | LogicalProj of rec_info

and rec_info = {
  comp : Constant.t option;
  comp_app : Constr.t;
  comp_proj : Constant.t;
  comp_recarg : int;
}

let is_structural = function Some (Structural _) -> true | _ -> false

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
         
let rec translate_cases_pattern env avoid ?loc = function
  | PatVar (Name id) -> loc, PUVar (id, false)
  | PatVar Anonymous -> 
      let n = next_ident_away (Id.of_string "wildcard") avoid in
        avoid := Id.Set.add n !avoid; loc, PUVar (n, true)
  | PatCstr ((ind, _ as cstr), pats, Anonymous) ->
     loc, PUCstr (cstr, (Inductiveops.inductive_nparams ind),
                  List.map (DAst.with_loc_val (translate_cases_pattern env avoid)) pats)
  | PatCstr (cstr, pats, Name id) ->
      CErrors.user_err ?loc ~hdr:"interp_pats" (str "Aliases not supported by Equations")

let rec ids_of_pats pats =
  fold_left (fun ids (_,p) ->
    match p with
    | PEApp ((loc,f), l) -> 
	let lids = ids_of_pats l in
        Id.Set.union (try Id.Set.add (ident_of_smart_global f) lids with _ -> lids) ids
    | PEWildcard -> ids
    | PEInac _ -> ids
    | PEPat _ -> ids)
    Id.Set.empty pats

let add_implicits impls avoid pats =
  let rec aux l pats =
    match l with
    | imp :: imps ->
       if Impargs.is_status_implicit imp then
         let id = Impargs.name_of_implicit imp in
	 let eqf = function ((Some (_, id')), p) -> Id.equal id' id | _ -> false in
	 try let pat = List.find_map (fun x -> if eqf x then Some (snd x) else None) pats in
	     let pats = List.remove_first eqf pats in
	     pat :: aux imps pats
	 with Not_found ->
	   let n = next_ident_away id avoid in
	   let pat = PEPat (CAst.make (CPatAtom (Some (CAst.make (Ident n))))) in
           avoid := Id.Set.add n !avoid;
	   (default_loc, pat) :: aux imps pats
       else begin
         match pats with
	 | hd :: tl -> (snd hd) :: aux imps tl
	 | [] -> List.map snd pats
       end
    | [] -> List.map snd pats
  in aux impls pats

let chole c loc =
  (* let tac = Genarg.in_gen (Genarg.rawwit Constrarg.wit_tactic) (solve_rec_tac_expr ()) in *)
  let kn = Lib.make_kn c in
  let cst = Names.Constant.make kn kn in
  CAst.make ~loc
  (CHole (Some (ImplicitArg (ConstRef cst, (0,None), false)),Misctypes.IntroAnonymous,None)), None

let rec interp_pat env ?(avoid = ref Id.Set.empty) (loc, p) =
  match p with
  | PEApp ((loc, f), l) ->
      let r =
        try Inl (Smartlocate.smart_global f)
        with e -> Inr (PUVar (ident_of_smart_global f, false))
      in begin match r with
      | Inl (ConstructRef c) ->
          let ind, _ = c in
          let nparams = Inductiveops.inductive_nparams ind in
          let nargs = Inductiveops.constructor_nrealargs c in
          let len = List.length l in
          let l' =
            if len < nargs then List.make (nargs - len) (loc, PEWildcard) @ l
            else l
          in
            Dumpglob.add_glob ~loc (ConstructRef c);
            Some loc, PUCstr (c, nparams, List.map (interp_pat env ~avoid) l')
      | Inl _ ->
          if l != [] then
            CErrors.user_err ~loc ~hdr:"interp_pat"
                     (str "Pattern variable " ++ pr_smart_global f ++ str " cannot be applied")
          else Some loc, PUVar (ident_of_smart_global f, false)
      | Inr p -> Some loc, p
      end
  | PEInac c -> Some loc, PUInac c
  | PEWildcard ->
      let n = next_ident_away (Id.of_string "wildcard") avoid in
        avoid := Id.Set.add n !avoid; Some loc, PUVar (n, true)
  | PEPat p ->
      let ids, pats = intern_pattern env p in
      let upat =
        match pats with
        | [(l, pat)] -> DAst.with_loc_val (translate_cases_pattern env avoid) pat
        | _ -> user_err_loc (Some loc, "interp_pat",
                             str "Or patterns not supported by Equations")
      in upat

let check_linearity pats =
  let rec aux ids pats = 
    List.fold_left (fun ids (loc, pat) ->
      match pat with
      | PUVar (n, _) ->
	if Id.Set.mem n ids then
	  CErrors.user_err ?loc ~hdr:"ids_of_pats"
	    (str "Non-linear occurrence of variable in patterns")
	else Id.Set.add n ids
      | PUInac _ -> ids
      | PUCstr (_, _, pats) -> aux ids pats)
      ids pats
  in ignore (aux Id.Set.empty pats)
	
let interp_eqn initi is_rec env impls eqn =
  let avoid = ref Id.Set.empty in
  let interp_pat = interp_pat env ~avoid in
  let rec aux recinfo i is_rec curpats (idopt, pats, rhs) =
    let curpats' = 
      match pats with
      | SignPats l -> l
      | RefinePats l -> curpats @ List.map (fun x -> None, x) l
    in
    avoid := Id.Set.union !avoid (ids_of_pats (List.map snd curpats'));
    Option.iter (fun (loc,id) ->
      if not (Id.equal id i) then
	user_err_loc (Some loc, "interp_pats",
		     str "Expecting a pattern for " ++ Id.print i);
      Dumpglob.dump_reference ~loc "<>" (Id.to_string id) "def")
      idopt;
    (*   if List.length pats <> List.length sign then *)
    (*     user_err_loc (loc, "interp_pats", *)
    (* 		 str "Patterns do not match the signature " ++  *)
    (* 		   pr_rel_context env sign); *)
    let curpats'' = add_implicits impls avoid curpats' in
    let loc =
      let beginloc = match idopt with
        | Some (loc, id) -> loc
        | _ -> match List.hd curpats' with
               | (Some (loc, _), _) -> loc
               | (None, (loc, _)) -> loc
      in
      let endloc = match List.last curpats' with
        | (_, (loc, _)) -> loc
      in Loc.merge beginloc endloc
    in
    let pats = map interp_pat curpats'' in
    let () = check_linearity pats in
      match is_rec with
      | Some (Structural l) ->
         (* let fnpat = (dummy_loc, PUVar (i, false)) in *)
         let addpat (id, k) =
           match k with
           | NestedOn None when Id.equal id initi -> None
           | _ -> Some (None, PUVar (id, false))
         in
         let structpats = List.map_filter addpat l in
         (loc, structpats @ pats,
          interp_rhs recinfo i is_rec curpats' rhs)
      | Some (Logical r) -> 
         (loc, pats, interp_rhs ((i, r) :: recinfo) i is_rec curpats' rhs)
      | None -> (loc, pats, interp_rhs recinfo i is_rec curpats' rhs)
  and interp_rhs recinfo i is_rec curpats = function
    | Refine (c, eqs) -> Refine (CAst.with_loc_val (interp_constr_expr recinfo !avoid) c, 
                                map (aux recinfo i is_rec curpats) eqs)
    | Program (c, w) ->
       let w = interp_wheres recinfo avoid w in
       Program (CAst.with_loc_val (interp_constr_expr recinfo !avoid) c, w)
    | Empty i -> Empty i
    | Rec (fni, r, id, s) -> 
      let rec_info = LogicalDirect (Option.get (Constrexpr_ops.constr_loc fni), i) in
      let recinfo = (i, rec_info) :: recinfo in
      Rec (fni, r, id, map (aux recinfo i is_rec curpats) s)
    | By (x, s) -> By (x, map (aux recinfo i is_rec curpats) s)
  and interp_wheres recinfo avoid w =
    let interp_where (((loc,id),nested,b,t) as p,eqns) =
      Dumpglob.dump_reference ~loc "<>" (Id.to_string id) "def";
      p, map (aux recinfo id None []) eqns
    in List.map interp_where w
  and interp_constr_expr recinfo ids ?(loc=default_loc) c =
    match c with
    (* |   | CAppExpl of loc * (proj_flag * reference) * constr_expr list *)
    | CApp ((None, { CAst.v = CRef ({ CAst.loc=loc'; v=Ident id'}, ie) }), args)
      when List.mem_assoc_f Id.equal id' recinfo ->
       let r = List.assoc_f Id.equal id' recinfo in
       let args =
         List.map (fun (c, expl) -> CAst.with_loc_val (interp_constr_expr recinfo ids) c, expl) args in
       let c = CApp ((None, CAst.(make ~loc (CRef (CAst.make ?loc:loc' (Ident id'), ie)))), args) in
       let arg = CAst.make ~loc (CApp ((None, CAst.make ~loc c), [chole id' loc])) in
       (match r with
        | LogicalDirect _ -> arg
        | LogicalProj r -> 
          let arg = if Option.is_empty r.comp then [arg, None] else [] in
          let qidproj = Nametab.shortest_qualid_of_global Id.Set.empty (ConstRef r.comp_proj) in
          CAst.make ~loc (CApp ((None, CAst.make ?loc:loc' (CRef (CAst.make ?loc:loc' (Qualid qidproj), None))),
                                args @ arg)))
    | _ -> map_constr_expr_with_binders Id.Set.add
             (fun ids -> CAst.with_loc_val (interp_constr_expr recinfo ids)) ids (CAst.make ~loc c)
  in aux [] initi is_rec [] eqn
