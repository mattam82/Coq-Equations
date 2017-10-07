(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names
open Printer
open Ppconstr


open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Vars
open Globnames
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Constrexpr
open Vars
open Tacexpr
open Tactics
open Tacticals
open Tacmach
open Context
open Evd
open Evarutil
open Evar_kinds
open Equations_common

open Constrintern
open Decl_kinds

(** User-level patterns *)
type user_pat =
    PUVar of identifier
  | PUCstr of constructor * int * user_pat list
  | PUInac of Constrexpr.constr_expr
type user_pats = user_pat list

(** AST *)
type program = 
  signature * clause list

and signature = identifier * rel_context * constr
  
and clause = Loc.t * lhs * clause rhs
  
and lhs = user_pats

and 'a rhs = 
  | Program of constr_expr * 'a where_clause list
  | Empty of identifier Loc.located
  | Rec of constr_expr * constr_expr option *
             identifier Loc.located option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list

and prototype =
  identifier located * Constrexpr.local_binder list * Constrexpr.constr_expr

and 'a where_clause = prototype * 'a list

let rec pr_user_pat env = function
  | PUVar i -> pr_id i
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
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ pr_id var
  | Rec (t, rel, id, s) -> 
     spc () ++ str "=>" ++ spc () ++ str"rec " ++ pr_constr_expr t ++ spc () ++
       pr_opt (fun (_, id) -> pr_id id) id ++ spc () ++
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
and pr_proto ((_,id), l, t) =
  pr_id id ++ pr_binders l ++ str" : " ++ pr_constr_expr t
and pr_clause env (loc, lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let ppclause clause =
  pp(pr_clause (Global.env ()) clause)

type pat_expr = 
  | PEApp of reference Misctypes.or_by_notation located * pat_expr located list
  | PEWildcard
  | PEInac of constr_expr
  | PEPat of cases_pattern_expr

type user_pat_expr = pat_expr located

type input_pats =
  | SignPats of (Id.t located option * user_pat_expr) list
  | RefinePats of user_pat_expr list

type pre_equation = 
  identifier located option * input_pats * pre_equation rhs

let next_ident_away s ids =
  let n' = Namegen.next_ident_away s !ids in
    ids := n' :: !ids; n'

type equation_option = | OInd of bool | ORec of Id.t located option 
		       | OComp of bool | OEquations of bool
    
type equation_user_option = equation_option

type equation_options = equation_option list

let pr_r_equation_user_option _prc _prlc _prt l =
  mt ()

let pr_equation_options  _prc _prlc _prt l =
  mt ()

type rec_type = 
  | Structural of Id.t located option
  | Logical of logical_rec

and logical_rec =
  | LogicalDirect of Id.t located
  | LogicalProj of rec_info

and rec_info = {
  comp : constant option;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}

let is_structural = function Some (Structural _) -> true | _ -> false

let is_rec_call r f =
  match r with
  | LogicalProj r -> Globnames.is_global (ConstRef r.comp_proj) f
  | LogicalDirect (loc, id) -> 
    match kind_of_term f with
    | Var id' -> Id.equal id id'
    | Const (c, _) ->
      let id' = Label.to_id (Constant.label c) in
      Id.equal id id'
    | _ -> false

let rec translate_cases_pattern env avoid = function
  | PatVar (loc, Name id) -> PUVar id
  | PatVar (loc, Anonymous) -> 
      let n = next_ident_away (id_of_string "wildcard") avoid in
	avoid := n :: !avoid; PUVar n
  | PatCstr (loc, (ind, _ as cstr), pats, Anonymous) ->
      PUCstr (cstr, (Inductiveops.inductive_nparams ind), map (translate_cases_pattern env avoid) pats)
  | PatCstr (loc, cstr, pats, Name id) ->
      user_err_loc (loc, "interp_pats", str "Aliases not supported by Equations")

let rec ids_of_pats pats =
  fold_left (fun ids (_,p) ->
    match p with
    | PEApp ((loc,f), l) -> 
	let lids = ids_of_pats l in
	  (try ident_of_smart_global f :: lids with _ -> lids) @ ids
    | PEWildcard -> ids
    | PEInac _ -> ids
    | PEPat _ -> ids)
    [] pats

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
	   let loc = dummy_loc in
	   let pat = PEPat (CPatAtom (loc, Some (Ident (loc, n)))) in
  	   avoid := n :: !avoid;
	   (loc, pat) :: aux imps pats
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
  CHole (loc,Some (ImplicitArg (ConstRef cst, (0,None), false)),Misctypes.IntroAnonymous,None), None
    
let interp_eqn i is_rec env impls eqn =
  let avoid = ref [] in
  let rec interp_pat (loc, p) =
    match p with
    | PEApp ((loc,f), l) -> 
	let r =
	  try Inl (Smartlocate.smart_global f)
	  with e -> Inr (PUVar (ident_of_smart_global f))
	in
	  (match r with
	   | Inl (ConstructRef c) ->
	       let (ind,_) = c in
	       let nparams = Inductiveops.inductive_nparams ind in
	       let nargs = constructor_nrealargs c in
	       let len = List.length l in
	       let l' =
		 if len < nargs then 
		   List.make (nargs - len) (loc,PEWildcard) @ l
		 else l
	       in 
		 Dumpglob.add_glob loc (ConstructRef c);
		 PUCstr (c, nparams, map interp_pat l')
	   | Inl _ ->
	       if l != [] then 
		 user_err_loc (loc, "interp_pats",
			       str "Pattern variable " ++ pr_smart_global f ++ str" cannot be applied ")
	       else PUVar (ident_of_smart_global f)
	   | Inr p -> p)
    | PEInac c -> PUInac c
    | PEWildcard -> 
	let n = next_ident_away (id_of_string "wildcard") avoid in
	  avoid := n :: !avoid; PUVar n

    | PEPat p ->
	let ids, pats = intern_pattern env p in
	  (* Names.identifier list * *)
	  (*   ((Names.identifier * Names.identifier) list * Rawterm.cases_pattern) list *)
	let upat = 
	  match pats with
	  | [(l, pat)] -> translate_cases_pattern env avoid pat
	  | _ -> user_err_loc (loc, "interp_pats", str "Or patterns not supported by equations")
	in upat
  in
  let rec aux recinfo (i, is_rec as fn) curpats (idopt, pats, rhs) =
    let curpats' = 
      match pats with
      | SignPats l -> l
      | RefinePats l -> curpats @ List.map (fun x -> None, x) l
    in
    avoid := !avoid @ ids_of_pats (List.map snd curpats');
    Option.iter (fun (loc,id) ->
      if not (Id.equal id i) then
	user_err_loc (loc, "interp_pats",
		     str "Expecting a pattern for " ++ pr_id i);
      Dumpglob.dump_reference loc "<>" (string_of_id id) "def")
      idopt;
    (*   if List.length pats <> List.length sign then *)
    (*     user_err_loc (loc, "interp_pats", *)
    (* 		 str "Patterns do not match the signature " ++  *)
    (* 		   pr_rel_context env sign); *)
    let curpats'' = add_implicits impls avoid curpats' in
    let loc =
      let beginloc = match idopt with
        | Some (loc, id) -> loc
        | None -> match List.hd curpats' with
                  | (Some (loc, _), _) -> loc
                  | (None, (loc, _)) -> loc
      in
      let endloc = match List.last curpats' with
        | (_, (loc, _)) -> loc
      in Loc.merge beginloc endloc
    in
    let pats = map interp_pat curpats'' in
      match is_rec with
      | Some (Structural _) -> (loc, PUVar i :: pats, interp_rhs recinfo fn curpats' rhs)
      | Some (Logical r) -> 
         (loc, pats, interp_rhs ((i, r) :: recinfo) fn curpats' rhs)
      | None -> (loc, pats, interp_rhs recinfo fn curpats' rhs)
  and interp_rhs recinfo (i, is_rec as fn) curpats = function
    | Refine (c, eqs) -> Refine (interp_constr_expr recinfo !avoid c, 
                                map (aux recinfo fn curpats) eqs)
    | Program (c, w) ->
       let w = interp_wheres recinfo avoid w in
       Program (interp_constr_expr recinfo !avoid c, w)
    | Empty i -> Empty i
    | Rec (i, r, id, s) -> 
      let rec_info = LogicalDirect (Constrexpr_ops.constr_loc i, fst fn) in
      let recinfo = (fst fn, rec_info) :: recinfo in
      Rec (i, r, id, map (aux recinfo fn curpats) s)
    | By (x, s) -> By (x, map (aux recinfo fn curpats) s)
  and interp_wheres recinfo avoid w =
    let interp_where (((loc,id),b,t) as p,eqns) =
      p, map (aux recinfo (id,None) []) eqns
    in List.map interp_where w
  and interp_constr_expr recinfo ids c = 
    match c with
    (* |   | CAppExpl of loc * (proj_flag * reference) * constr_expr list *)
    | CApp (loc, (None, CRef (Ident (loc',id'), ie)), args)
      when List.mem_assoc_f Id.equal id' recinfo ->
       let r = List.assoc_f Id.equal id' recinfo in
       let args =
         List.map (fun (c, expl) -> interp_constr_expr recinfo ids c, expl) args in
       let c = CApp (loc, (None, CRef (Ident (loc', id'), ie)), args) in
       let arg = CApp (loc, (None, c), [chole id' loc]) in
       (match r with
        | LogicalDirect _ -> arg 
        | LogicalProj r -> 
          let arg = if Option.is_empty r.comp then [arg, None] else [] in
          let qidproj = Nametab.shortest_qualid_of_global Idset.empty (ConstRef r.comp_proj) in
          CApp (loc, (None, CRef (Qualid (loc', qidproj), None)), args @ arg))
    | _ -> map_constr_expr_with_binders (fun id l -> id :: l)
	     (interp_constr_expr recinfo) ids c
  in aux [] (i, is_rec) [] eqn
