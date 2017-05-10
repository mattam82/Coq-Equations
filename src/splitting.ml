(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

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
open Depelim
open Termops
open Syntax
open Covering

let map_where f w =
  { w with
    where_nctx = map_named_context f w.where_nctx;
    where_prob = map_ctx_map f w.where_prob;
    where_term = f w.where_term;
    where_arity = f w.where_arity;
    where_type = f w.where_type }
    
let map_split f split =
  let rec aux = function
    | Compute (lhs, where, ty, RProgram c) ->
      let where' = 
        List.map
          (fun w -> let w' = map_where f w in
                 { w' with where_splitting = aux w.where_splitting })
          where
      in
      let lhs' = map_ctx_map f lhs in
	Compute (lhs', where', f ty, RProgram (f c))
    | Split (lhs, y, z, cs) ->
      let lhs' = map_ctx_map f lhs in
      Split (lhs', y, f z, Array.map (Option.map aux) cs)
    | Mapping (lhs, s) ->
       let lhs' = map_ctx_map f lhs in
       Mapping (lhs', aux s)
    | RecValid (id, c) -> RecValid (id, aux c)
    | Valid (lhs, y, z, w, u, cs) ->
      let lhs' = map_ctx_map f lhs in
	Valid (lhs', f y, z, w, u, 
	       List.map (fun (gl, cl, subst, invsubst, s) -> 
		 (gl, List.map f cl, map_ctx_map f subst, invsubst, aux s)) cs)
    | Refined (lhs, info, s) ->
      let lhs' = map_ctx_map f lhs in
      let (id, c, cty) = info.refined_obj in
      let (scf, scargs) = info.refined_app in
	Refined (lhs', { info with refined_obj = (id, f c, f cty);
	  refined_app = (f scf, List.map f scargs);
	  refined_rettyp = f info.refined_rettyp;
	  refined_revctx = map_ctx_map f info.refined_revctx;
	  refined_newprob = map_ctx_map f info.refined_newprob;
	  refined_newprob_to_lhs = map_ctx_map f info.refined_newprob_to_lhs;
	  refined_newty = f info.refined_newty}, aux s)
    | Compute (lhs, where, ty, (REmpty _ as em)) ->
      (* let lhs' = map_ctx_map f lhs in *)
	Compute (lhs, where, f ty, em)
  in aux split

let helper_evar evm evar env typ src =
  let sign, typ', instance, _, _ = push_rel_context_to_named_context env typ in
  let evm' = evar_declare sign evar typ' ~src evm in
    evm', mkEvar (evar, Array.of_list instance)

let term_of_tree status isevar env0 tree =
  let oblevars = ref Evar.Map.empty in
  let helpers = ref [] in
  let rec aux env evm = function
    | Compute ((ctx, _, _), where, ty, RProgram rhs) -> 
       let evm, ctx = 
         List.fold_right 
           (fun {where_id; where_nctx; where_prob; where_term;
               where_type; where_splitting }
              (evm, ctx) ->
             let env = push_named_context where_nctx env0 in
             (* FIXME push ctx too if mutual wheres *)
             let evm, c', ty' = aux env evm where_splitting in
             let inst = List.map get_id where_nctx in
             (** In de Bruijn context *)
             let tydb = subst_vars inst ty' in
             let evm, c', ty' =
               match kind_of_term where_term with
               | Evar (ev, _) ->
                 let term' = mkLetIn (Name (id_of_string "prog"), c', ty', lift 1 ty') in
                 let evm, term = helper_evar evm ev env term' (dummy_loc, QuestionMark (Define false)) in
                 let ev = fst (destEvar term) in
                  oblevars := Evar.Map.add ev (List.length where_nctx) !oblevars;
                  helpers := (ev, 0) :: !helpers;
                  evm, subst_vars inst term, tydb
               | _ -> assert(false)
             in
             (evm, (make_def (Name where_id) (Some c') ty' :: ctx)))
           where (evm,ctx)
       in
       let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst ty ctx in
       evm, body, typ

    | Compute ((ctx, _, _), where, ty, REmpty split) ->
       assert (List.is_empty where);
	let split = make_def (Name (id_of_string "split"))
          (Some (coq_nat_of_int (succ (length ctx - split))))
          (Lazy.force coq_nat)
       in
       let ty' = it_mkProd_or_LetIn ty ctx in
       let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
       let evm, term = 
         new_evar env evm ~src:(dummy_loc, QuestionMark (Define false)) let_ty' in
       let ev = fst (destEvar term) in
       oblevars := Evar.Map.add ev 0 !oblevars;
       evm, term, ty'

    | Mapping ((ctx, p, ctx'), s) ->
       let evm, term, ty = aux env evm s in
       let args = Array.rev_of_list (constrs_of_pats ~inacc:false env p) in
       let term = it_mkLambda_or_LetIn (whd_beta evm (mkApp (term, args))) ctx in
       let ty = it_mkProd_or_subst (prod_appvect ty args) ctx in
         evm, term, ty
		    
    | RecValid (id, rest) -> aux env evm rest

    | Refined ((ctx, _, _), info, rest) ->
	let (id, _, _), ty, rarg, path, ev, (f, args), newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_path,
	  info.refined_ex, info.refined_app, info.refined_newprob, info.refined_newty
	in
	let evm, sterm, sty = aux env evm rest in
	let evm, term, ty = 
	  let term = mkLetIn (Name (id_of_string "prog"), sterm, sty, lift 1 sty) in
	  let evm, term = helper_evar evm ev (Global.env ()) term
	    (dummy_loc, QuestionMark (Define false)) 
	  in
	    oblevars := Evar.Map.add ev 0 !oblevars;
	    helpers := (ev, rarg) :: !helpers;
	    evm, term, ty
	in
	let term = applist (f, args) in
	let term = it_mkLambda_or_LetIn term ctx in
	let ty = it_mkProd_or_subst ty ctx in
	  evm, term, ty

    | Valid ((ctx, _, _), ty, substc, tac, (entry, pv), rest) ->
	let tac = Proofview.tclDISPATCH 
	  (map (fun (goal, args, subst, invsubst, x) -> 
	    Refine.refine { Sigma.run = fun evm ->
	      let evm, term, ty = aux env (Sigma.to_evar_map evm) x in
       Sigma.here (applistc term args) (Sigma.Unsafe.of_evar_map evm)}) rest)
	in
	let pv : Proofview_monad.proofview = Obj.magic pv in
	let pv = { pv with Proofview_monad.solution = evm } in
	let _, pv', _, _ = Proofview.apply env tac (Obj.magic pv) in
	let c = List.hd (Proofview.partial_proof entry pv') in
	  Proofview.return pv', 
	  it_mkLambda_or_LetIn (subst_vars substc c) ctx, it_mkProd_or_LetIn ty ctx
	      
    | Split ((ctx, _, _), rel, ty, sp) -> 
	let before, decl, after = split_tele (pred rel) ctx in
	let evd = ref evm in
	let branches = 
	  Array.map (fun split -> 
	    match split with
	    | Some s -> let evm', c, t = aux env !evd s in evd := evm'; c,t
	    | None ->
		(* dead code, inversion will find a proof of False by splitting on the rel'th hyp *)
	      coq_nat_of_int rel, Lazy.force coq_nat)
	    sp 
	in
	let evm = !evd in
	let branches_ctx =
	  Array.mapi (fun i (br, brt) -> make_def (Name (id_of_string ("m_" ^ string_of_int i))) (Some br) brt)
	    branches
	in
	let n, branches_lets =
	  Array.fold_left (fun (n, lets) decl ->
	    (succ n, map_rel_declaration (lift n) decl :: lets))
	    (0, []) branches_ctx
	in
	let liftctx = lift_context (Array.length branches) ctx in
	let evm, case =
	  let ty = it_mkProd_or_LetIn ty liftctx in
	  let ty = it_mkLambda_or_LetIn ty branches_lets in
          let nbbranches =
            make_def (Name (id_of_string "branches"))
	      (Some (coq_nat_of_int (length branches_lets))) (Lazy.force coq_nat)
	  in
	  let nbdiscr = make_def (Name (id_of_string "target"))
			(Some (coq_nat_of_int (length before)))
			(Lazy.force coq_nat)
	  in
	  let ty = it_mkLambda_or_LetIn (lift 2 ty) [nbbranches;nbdiscr] in
	  let evm, term = new_evar env evm ~src:(dummy_loc, QuestionMark status) ty in
	  let ev = fst (destEvar term) in
	    oblevars := Evar.Map.add ev 0 !oblevars;
	    evm, term
	in       
	let casetyp = it_mkProd_or_subst ty ctx in
	  evm, mkCast(case, DEFAULTcast, casetyp), casetyp
  in 
  let evm, term, typ = aux env0 !isevar tree in
    isevar := evm;
    !helpers, !oblevars, term, typ

let is_comp_obl comp hole_kind =
  match comp with
  | None -> false
  | Some r -> 
      match hole_kind, r with 
      | ImplicitArg (ConstRef c, (n, _), _), LogicalProj r ->
	Constant.equal c r.comp_proj && n == r.comp_recarg 
      | ImplicitArg (ConstRef c, (n, _), _), LogicalDirect (loc, id) ->
        is_rec_call r (mkConst c)
      | _ -> false

let zeta_red =
  let red = Tacred.cbv_norm_flags
      CClosure.(RedFlags.red_add RedFlags.no_red RedFlags.fZETA)
  in
    reduct_in_concl (red, DEFAULTcast)

let define_tree is_recursive poly impls status isevar env (i, sign, arity)
                comp split hook =
  let _ = isevar := Evarutil.nf_evar_map_undefined !isevar in
  let helpers, oblevs, t, ty = term_of_tree status isevar env split in
  let split = map_split (nf_evar !isevar) split in
  let nf, subst = Evarutil.e_nf_evars_and_universes isevar in
  let obls, (emap, cmap), t', ty' = 
    Obligations.eterm_obligations env i !isevar
      0 ~status (nf t) (whd_betalet !isevar (nf ty))
  in
  let obls = 
    Array.map (fun (id, ty, loc, s, d, t) ->
      let assc = rev_assoc Id.equal id emap in
      let tac = 
	if Evar.Map.mem assc oblevs 
	then 
          let intros = Evar.Map.find assc oblevs in
          Some (Tacticals.New.tclTHEN (Tacticals.New.tclDO intros (of82 intro)) (equations_tac ()))
	else if is_comp_obl comp (snd loc) then
	  let unfolds =
            match Option.get comp with
            | LogicalDirect _ -> tclIDTAC
            | LogicalProj r ->
              Option.cata
                (fun comp -> to82 (unfold_in_concl
	            [((Locus.AllOccurrencesBut [1]), EvalConstRef comp)]))
                tclIDTAC r.comp
          in
	    Some (of82 (tclTRY
			  (tclTHENLIST [to82 zeta_red; to82 Tactics.intros; unfolds;
					(to82 (solve_rec_tac ()))])))
	else Some ((!Obligations.default_tactic))
      in (id, ty, loc, s, d, tac)) obls
  in
  let term_info = map (fun (ev, arg) ->
    (ev, arg, List.assoc ev emap)) helpers
  in
  let hook x y = 
    let _l =
      Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Ident (dummy_loc, id)) obls in
      (* FIXME Table.extraction_inline true l; *)
      hook split cmap term_info x y
  in
  let hook = Lemmas.mk_hook hook in
  let reduce = 
    let open CClosure.RedFlags in
    let flags = CClosure.betaiotazeta in
    (* let flags = match comp with None -> flags *)
    (*   | Some f -> fCONST f.comp :: fCONST f.comp_proj :: flags *)
    (* in *)
      clos_norm_flags flags (Global.env ()) Evd.empty
  in
  let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let ty' = it_mkProd_or_LetIn arity sign in
  let ty' = nf ty' in
    match is_recursive with
    | Some (Structural id) ->
        let ty' = it_mkProd_or_LetIn ty' [make_assum Anonymous ty'] in
	ignore(Obligations.add_mutual_definitions [(i, t', ty', impls, obls)] 
		 (Evd.evar_universe_context !isevar) [] ~kind
		 ~reduce ~hook (Obligations.IsFixpoint [id, CStructRec]))
    | _ ->
      ignore(Obligations.add_definition ~hook ~kind
	       ~implicits:impls i ~term:t' ty'
	       ~reduce (Evd.evar_universe_context !isevar) obls)

let mapping_rhs s = function
  | RProgram c -> RProgram (mapping_constr s c)
  | REmpty i -> 
      try match nth (pi2 s) (pred i) with 
      | PRel i' -> REmpty i'
      | _ -> assert false
      with Not_found -> assert false

let map_rhs f g = function
  | RProgram c -> RProgram (f c)
  | REmpty i -> REmpty (g i)

let clean_clause (ctx, pats, ty, c) =
  (ctx, pats, ty, 
  map_rhs (nf_beta Evd.empty) (fun x -> x) c)

let map_evars_in_constr evd evar_map c = 
  evar_map (fun id ->
	    let gr = Nametab.global (Qualid (dummy_loc, qualid_of_ident id)) in
	    let (f, uc) = Universes.unsafe_constr_of_global gr in f)
	   (nf_evars_universes evd c)

let map_evars_in_split evd m = map_split (map_evars_in_constr evd m)
