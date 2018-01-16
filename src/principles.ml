(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2017 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Principles derived from equation definitions. *)

open Term
open Names
open Libnames
open Vars
open Equations_common
open Syntax
open Covering
open Splitting
open Principles_proofs

open EConstr
open Vars (* lift, subst etc... *)

type statement = constr * types option
type statements = statement list

type recursive = bool

type node_kind =
  | Regular
  | Refine
  | Where
  | Nested of recursive

let kind_of_prog p =
  match p.program_rec_annot with
  | Some (NestedOn (Some _)) -> Nested true
  | Some (NestedOn None) -> Nested false
  | _ -> Regular

let regular_or_nested = function
  | Regular | Nested _ -> true
  | _ -> false

let regular_or_nested_rec = function
  | Regular -> true
  | Nested r -> r
  | _ -> false

let pi1 (x,_,_) = x
let pi2 (_,y,_) = y
let pi3 (_,_,z) = z

let match_arguments sigma l l' =
  let rec aux i =
    if i < Array.length l' then
      if i < Array.length l then
        if eq_constr sigma l.(i) l'.(i) then
          i :: aux (succ i)
        else aux (succ i)
      else aux (succ i)
    else [i]
  in aux 0

let filter_arguments f l =
  let rec aux i f l =
    match f, l with
    | n :: f', a :: l' ->
       if i < n then aux (succ i) f l'
       else if i = n then
         a :: aux (succ i) f' l'
       else assert false
    | _, _ -> l
  in aux 0 f l

let clean_rec_calls sigma (ctx, ctxlen, c) =
  let open Context.Rel.Declaration in
  let is_seen def prev =
    List.exists (eq_constr sigma def) prev
  in
  let rec aux (ctx, ctxlen, c) k ctx' seen =
    match ctx with
    | (LocalAssum _ as ass) :: ((LocalDef (recres, call, _) as def) :: rest) ->
       let subst = [mkProp; call] in
       if is_seen call seen then
         aux (rest, ctxlen - 2, substnl subst k c) k
             (subst_rel_context 0 subst ctx')
             (List.map (substnl subst 0) seen)
       else
         aux (rest, ctxlen, c) (k + 2) (List.append ctx' [ass; def])
             (List.map (substnl subst 0) (call :: seen))
    | rest -> (List.append ctx' rest, k + List.length rest, c)
  in
  aux (ctx, ctxlen, c) 0 [] []

let head sigma c = fst (decompose_app sigma c)

let find_firsti f l =
  let rec aux i = function
    | hd :: tl ->
       (match f i hd with
        | Some x -> x
        | None -> aux (succ i) tl)
    | [] -> raise Not_found
  in aux 0 l

let is_applied_to_structarg i is_rec lenargs =
  match is_rec with
  | Some (Structural ids) -> begin
     try
       let fn, kind, _ = List.nth ids i in
       match kind with
       | StructuralOn idx | NestedOn (Some idx) -> lenargs > idx
       | NestedOn None -> true
     with Invalid_argument _
        | Failure _ -> true
    end
  | _ -> true

let abstract_rec_calls sigma ?(do_subst=true) is_rec len protos c =
  let lenprotos = List.length protos in
  let proto_fs = List.map (fun ((f,args), _, _, _, _) -> f) protos in
  let find_rec_call f args =
    let fm i ((f',filter), alias, idx, sign, arity) =
      let f', args' = Termops.decompose_app_vect sigma f' in
      if eq_constr sigma f' f then
        if is_applied_to_structarg i is_rec (List.length args) then
          Some (idx, sign, arity, filter_arguments filter args)
        else None
      else
	match alias with
        | Some (f',argsf) ->
           let f', args' = Termops.decompose_app_vect sigma f' in
           if eq_constr sigma (head sigma f') f then
             Some (idx, sign, arity, filter_arguments argsf args)
           else None
        | None -> None
    in
    try Some (find_firsti fm protos)
    with Not_found -> None
  in
  let find_rec_call f args =
    match find_rec_call f args with
    | Some (i, sign, arity, args') -> Some (i, sign, arity, args')
    | None -> 
	match is_rec with
        | Some (Logical r) when is_rec_call sigma r f ->
           (match r with
           | LogicalDirect _ -> None
           | LogicalProj r -> 
	      Some (lenprotos - 1, [] (* FIXME *), r.comp_app, CList.drop_last args))
	| _ -> None
  in
  let rec aux n env c =
    match kind sigma c with
    | App (f', args) ->
	let (ctx, lenctx, args) = 
	  Array.fold_left (fun (ctx,len,c) arg -> 
	    let ctx', lenctx', arg' = aux n env arg in
	    let len' = lenctx' + len in
            let ctx'' = lift_rel_context len ctx' in
	    let c' = (liftn len (succ lenctx') arg') :: List.map (lift lenctx') c in
	      (ctx''@ctx, len', c'))
	    ([],0,[]) args
	in
	let args = List.rev args in
	let f' = lift lenctx f' in
	(match find_rec_call f' args with
	 | Some (i, sign, arity, args') ->
            let ressign, resty =
              let rec aux sign args =
                match sign, args with
                | Context.Rel.Declaration.LocalAssum (na, t) :: sign, a :: args ->
                   aux (subst_telescope a sign) args
                | Context.Rel.Declaration.LocalDef (na, b, t) :: sign, args ->
                   aux (subst_telescope b sign) args
                | sign, [] ->
                   let ctx = List.rev sign in
                   let arity = substnl (List.rev args') (List.length sign) (of_constr arity) in
                   ctx, it_mkProd_or_LetIn arity ctx
                | [], _ :: _ -> assert false (* by typing *)
              in aux (List.rev sign) args'
            in
	    let result =
              make_def (Name (id_of_string "recres")) (Some (mkApp (f', Array.of_list args))) resty in
            let extsign = smash_rel_context sigma ressign in
            let lenext = List.length extsign in
	    let hypty = mkApp (mkApp (mkRel (i + len + lenctx + 2 + n + lenext),
				      Array.append (Array.map (lift (1 + lenext)) (Array.of_list args'))
                                        (extended_rel_vect 0 extsign)),
                               [| mkApp (mkRel (lenext + 1), extended_rel_vect 0 extsign) |])
	    in
            let hypty = it_mkProd_or_LetIn hypty extsign in
	    let hyp = make_assum (Name (id_of_string "Hind")) hypty in
	    [hyp;result]@ctx, lenctx + 2, mkRel 2
	 | None -> (ctx, lenctx, mkApp (f', Array.of_list args)))
	    
    | Lambda (na,t,b) ->
	let ctx',lenctx',b' = aux (succ n) ((na,None,t) :: env) b in
	  (match ctx' with
	   | [] -> [], 0, c
	   | hyp :: rest -> 
	      let ty = mkProd (na, t, it_mkProd_or_LetIn (get_type hyp) rest) in
	      [make_assum (Name (id_of_string "Hind")) ty], 1, lift 1 c)

    (* | Cast (_, _, f) when is_comp f -> aux n f *)
	  
    | LetIn (na,b,t,c) ->
	let ctx',lenctx',b' = aux n env b in
	let ctx'',lenctx'',c' = aux (succ n) ((na,Some b,t) :: env) c in
	let ctx'' = lift_rel_contextn 1 lenctx' ctx'' in
	let fullctx = ctx'' @ [make_def na  (Some b') (lift lenctx' t)] @ ctx' in
	  fullctx, lenctx'+lenctx''+1, liftn lenctx' (lenctx'' + 2) c'

    | Prod (na, d, c) when not (Termops.dependent sigma (mkRel 1) c)  ->
	let ctx',lenctx',d' = aux n env d in
	let ctx'',lenctx'',c' = aux n env (subst1 mkProp c) in
          lift_rel_context lenctx' ctx'' @ ctx', lenctx' + lenctx'',
	mkProd (na, lift lenctx'' d', 
	       liftn lenctx' (lenctx'' + 2) 
		 (lift 1 c'))

    | Case (ci, p, c, br) ->
	let ctx', lenctx', c' = aux n env c in
	let case' = mkCase (ci, lift lenctx' p, c', Array.map (lift lenctx') br) in
	  ctx', lenctx', substnl proto_fs (succ len + lenctx') case'

    | Proj (p, c) ->
       let ctx', lenctx', c' = aux n env c in
         ctx', lenctx', mkProj (p, c')
			     
    | _ -> [], 0, if do_subst then (substnl proto_fs (len + n) c) else c
  in clean_rec_calls sigma (aux 0 [] c)
                
let subst_app sigma f fn c =
  let rec aux n c =
    match kind sigma c with
    | App (f', args) when eq_constr sigma f f' ->
      let args' = Array.map (map_with_binders sigma succ aux n) args in
      fn n f' args'
    | Var _ when eq_constr sigma f c ->
       fn n c [||] 
    | _ -> map_with_binders sigma succ aux n c
  in aux 0 c
  
let subst_comp_proj sigma f proj c =
  subst_app sigma proj (fun n x args ->
    mkApp (f, Array.sub args 0 (Array.length args - 1)))
    c

(** Substitute occurrences of [proj] by [f] in the splitting. *)
let subst_comp_proj_split sigma f proj s =
  map_split (subst_comp_proj sigma f proj) s

let reference_of_id s = 
  Ident (None, s)

let clear_ind_assums sigma ind ctx =
  let rec clear_assums c =
    match kind sigma c with
    | Prod (na, b, c) ->
       let sign, arity = decompose_prod_assum sigma b in
       let t, _ = decompose_app sigma arity in
       if isInd sigma t then
         let (ind', _), _ = destInd sigma t in
	 if eq_mind ind' ind then (
           assert(not (Termops.dependent sigma (mkRel 1) c));
	   clear_assums (subst1 mkProp c))
	 else mkProd (na, b, clear_assums c)
       else mkProd (na, b, clear_assums c)
    | LetIn (na, b, t, c) ->
	mkLetIn (na, b, t, clear_assums c)
    | _ -> c
  in map_rel_context clear_assums ctx


let type_of_rel t ctx =
  match kind_of_term t with
  | Rel k -> lift k (get_type (List.nth ctx (pred k)))
  | c -> mkProp

let compute_elim_type env evd is_rec protos k leninds
                      ind_stmts all_stmts sign app elimty =
  let ctx, arity = decompose_prod_assum !evd elimty in
  let lenrealinds =
    List.length (List.filter (fun (_, (_,_,_,_,_,_,_,(kind,_)),_) -> regular_or_nested_rec kind) ind_stmts) in
  let newctx =
    if lenrealinds == 1 then CList.skipn (List.length sign + 2) ctx
    else ctx
  in
  (* Assumes non-dep mutual eliminator of the graph *)
  let newarity =
    if lenrealinds == 1 then
      it_mkProd_or_LetIn (substl [mkProp; app] arity) sign
    else
      let clean_one a sign fn =
        let ctx, concl = decompose_prod_assum !evd a in
        let newctx = CList.skipn 2 ctx in
        let newconcl = substl [mkProp; mkApp (fn, extended_rel_vect 0 sign)] concl in
        it_mkProd_or_LetIn newconcl newctx
      in
      let rec aux arity ind_stmts =
        match kind !evd arity, ind_stmts with
        | _, (i, ((fn, _), _, _, sign, ar, _, _, ((Where | Refine), cut)), _) :: stmts ->
           aux arity stmts
        | App (conj, [| arity; rest |]),
          (i, ((fn, _), _, _, sign, ar, _, _, (refine, cut)), _) :: stmts ->
           mkApp (conj, [| clean_one arity sign fn ; aux rest stmts |])
        | _, [ (i, ((fn, _), _, _, sign, ar, _, _, _), _) ] ->
           clean_one arity sign fn
        | _, [] -> arity
        | _, _ -> assert false
      in aux arity ind_stmts
  in
  let newctx' = clear_ind_assums !evd k newctx in
  if leninds == 1 then List.length newctx', it_mkProd_or_LetIn newarity newctx' else
  let sort = fresh_logic_sort evd in
  let methods, preds = CList.chop (List.length newctx - leninds) newctx' in
  let ppred, preds = CList.sep_last preds in
  let newpredfn i d (idx, (f', alias, path, sign, arity, pats, args, (refine, cut)), _) =
    if refine != Refine then d else
    let (n, b, t) = to_tuple d in
    let signlen = List.length sign in
    let ctx = of_tuple (Anonymous, None, arity) :: sign in
    let app =
      let argsinfo =
	CList.map_i
	  (fun i (c, arg) -> 
	   let idx = signlen - arg + 1 in (* lift 1, over return value *)
	   let ty = lift (idx (* 1 for return value *)) 
			 (get_type (List.nth sign (pred (pred idx)))) 
	   in
	   (idx, ty, lift 1 c, mkRel idx)) 
	  0 args
      in
      let lenargs = List.length argsinfo in
      let transport = e_new_global evd (get_eq_case ()) in
      let transport ty x y eq c cty =
	mkApp (transport,
	       [| ty; x;
		  mkLambda (Name (id_of_string "abs"), ty,
                            Termops.replace_term !evd (lift 1 x) (mkRel 1) (lift 1 cty));
		  c; y; eq (* equality *) |])
      in
      let pargs, subst =
	match argsinfo with
	| [] -> List.map (lift (lenargs+1)) pats, []
	| (i, ty, c, rel) :: [] ->
	   List.fold_right
	   (fun t (pargs, subst) ->
	    let _idx = i + 2 * lenargs in
	    let rel = lift lenargs rel in
            let tty = lift (lenargs+1) (type_of_rel (to_constr !evd t) sign) in
            if Termops.dependent !evd rel tty then
	      let tr =
                if isRel !evd c then lift (lenargs+1) t
		else
		  transport (lift lenargs ty) rel (lift lenargs c)
                            (mkRel 1) (lift (lenargs+1) (t)) tty
	      in
	      let t' =
                if isRel !evd c then lift (lenargs+3) (t)
		else transport (lift (lenargs+2) ty)
			       (lift 2 rel)
			       (mkRel 2)
                               (mkRel 1) (lift (lenargs+3) (t)) (lift 2 tty)
	      in (tr :: pargs, (rel, t') :: subst)
	    else (* for equalities + return value *)
              let t' = lift (lenargs+1) (t) in
              let t' = Termops.replace_term !evd (lift (lenargs) c) rel t' in
	      (t' :: pargs, subst)) pats ([], [])
	| _ -> assert false
      in
      let result, _ = 
	List.fold_left
  	(fun (acc, pred) (i, ty, c, rel) -> 
	 let idx = i + 2 * lenargs in
         if Termops.dependent !evd (mkRel idx) pred then
	   let eqty =
	     mkEq env evd (lift (lenargs+1) ty) (mkRel 1)
		  (lift (lenargs+1) rel)
	   in
	   let pred' = 
	     List.fold_left
               (fun acc (t, tr) -> Termops.replace_term !evd t tr acc)
               (lift 1 (Termops.replace_term !evd (mkRel idx) (mkRel 1) pred))
	       subst
	   in
           let transportd =
             e_new_global evd (get_eq_elim ())
           in
	   let app = 
	     mkApp (transportd,
		    [| lift lenargs ty; lift lenargs rel;
  		       mkLambda (Name (id_of_string "refine"), lift lenargs ty,
				 mkLambda (Name (id_of_string "refine_eq"), eqty, pred'));
		       acc; (lift lenargs c); mkRel 1 (* equality *) |])
	   in (app, subst1 c pred)
	 else (acc, subst1 c pred))
	(mkRel (succ lenargs), lift (succ (lenargs * 2)) arity)
	argsinfo
      in
      let ppath = (* The preceding P *) 
	match path with
	| [] -> assert false
	| ev :: path -> 
	   let res = 
	     list_find_map_i (fun i' (_, (_, _, path', _, _, _, _, _), _) ->
			      if eq_path path' path then Some (idx + 1 - i')
			      else None) 1 ind_stmts
	   in match res with None -> assert false | Some i -> i
      in
      let papp =
	applistc (lift (succ signlen + lenargs) (mkRel ppath)) 
		 pargs
      in
      let papp = applistc papp [result] in
      let refeqs = List.map (fun (i, ty, c, rel) -> mkEq env evd ty c rel) argsinfo in
      let app c = List.fold_right
		  (fun c acc ->
		   mkProd (Name (id_of_string "Heq"), c, acc))
		  refeqs c
      in
      let indhyps =
	List.concat
	(List.map (fun (c, _) ->
	      let hyps, hypslen, c' = 
                abstract_rec_calls !evd ~do_subst:false
		   is_rec signlen protos (Reductionops.nf_beta !evd (lift 1 c)) 
	      in 
	      let lifthyps = lift_rel_contextn (signlen + 2) (- (pred i)) hyps in
	        lifthyps) args)
      in
        it_mkLambda_or_LetIn
	  (app (it_mkProd_or_clean (lift (List.length indhyps) papp) 
                                   (lift_rel_context lenargs indhyps)))
	  ctx
    in
    let ty = it_mkProd_or_LetIn sort ctx in
    of_tuple (n, Some app, ty)
  in
  let newpreds = CList.map2_i newpredfn 1 preds (List.rev (List.tl ind_stmts)) in
  let skipped, methods' = (* Skip the indirection methods due to refinements, 
			      as they are trivially provable *)
    let rec aux stmts meths n meths' = 
      match stmts, meths with
      | (Refine, _, _, _) :: stmts, decl :: decls ->
	 aux stmts (subst_telescope mkProp decls) (succ n) meths'
      | (_, _, _, _) :: stmts, decl :: decls ->
	 aux stmts decls n (decl :: meths')
      | [], [] -> n, meths'
      | [], decls -> n, List.rev decls @ meths'
      | _, _ -> assert false
    in aux all_stmts (List.rev methods) 0 []
  in
  let ctx = methods' @ newpreds @ [ppred] in
  let elimty = it_mkProd_or_LetIn (lift (-skipped) newarity) ctx in
  let undefpreds = List.length (List.filter (fun decl -> Option.is_empty (get_value decl)) newpreds) in
  let nargs = List.length methods' + undefpreds + 1 in
  nargs, elimty

let replace_vars_context inst ctx =
  List.fold_right
    (fun decl (k, acc) ->
      let decl' = map_rel_declaration (substn_vars k inst) decl in
      (succ k, decl' :: acc))
    ctx (1, [])

let pr_where env sigma ctx {where_id; where_nctx; where_prob; where_term;
                      where_type; where_splitting } =
  let open Pp in
  let envc = Environ.push_rel_context ctx env in
  let envw = push_named_context where_nctx env in
  Termops.print_constr_env envc sigma where_term ++ fnl () ++
    str"where " ++ Nameops.pr_id where_id ++ str" : " ++
    Termops.print_constr_env envc sigma where_type ++
    str" := " ++ fnl () ++
    pr_context_map envw sigma where_prob ++ fnl () ++
    pr_splitting envw sigma where_splitting

let where_instance w =
  List.map (fun w -> w.where_term) w

let arguments sigma c = snd (Termops.decompose_app_vect sigma c)

let unfold_constr sigma c =
  to82 (Tactics.unfold_in_concl [(Locus.AllOccurrences, EvalConstRef (fst (destConst sigma c)))])

let extend_prob_ctx delta (ctx, pats, ctx') =
  (delta @ ctx, lift_pats (List.length delta) pats, ctx')

let subst_rec_split env evd f comp comprecarg prob s split =
  let map_proto f ty =
    match comprecarg with
    | Some recarg ->
       let lctx, ty' = decompose_prod_assum evd ty in
       let app =
         if comp then (* when Globnames.is_global (ConstRef const) fcomp -> *) 
           (let fcomp, args = decompose_app evd ty' in
           (* When a comp *) applistc f args)
         else
           let args = Termops.rel_list 0 (List.length lctx) in
           let before, after = 
             if (* recarg == -1 *) true then CList.drop_last args, []
             else let bf, after = CList.chop (pred recarg) args in
               bf, List.tl after
           in
            applistc f (before @ after)
       in
       it_mkLambda_or_LetIn app lctx
    | None -> f
  in
  let subst_rec cutprob s (ctx, p, _ as lhs) =
    let subst = List.fold_left (fun (ctx, _, ctx' as lhs') (id, b) ->
        try let rel, _, ty = Termops.lookup_rel_id id ctx in
            let fK = map_proto b (lift rel ty) in
            let substf = single_subst env evd rel (PInac fK) ctx
            (* ctx[n := f] |- _ : ctx *) in
            compose_subst env ~sigma:evd substf lhs'
        with Not_found (* lookup *) -> lhs') (id_subst ctx) s
    in
    let csubst = 
      compose_subst env ~sigma:evd
        (compose_subst env ~sigma:evd subst lhs) cutprob
    in subst, csubst
  in
  let subst_rec_named s acc = 
    List.fold_left (fun (acc, ctx) (id, b) ->
        try let (_, _, ty) = to_named_tuple (Equations_common.lookup_named id ctx) in
            let fK = map_proto b ty in
            (id, fK) :: acc, subst_in_named_ctx id fK ctx
        with Not_found -> acc, ctx)
                   ([], acc) s
  in
  let rec aux cutprob s path = function
    | Compute ((ctx,pats,del as lhs), where, ty, c) ->
       let subst, lhs' = subst_rec cutprob s lhs in
       let progctx = (extend_prob_ctx (where_context where) lhs) in
       let substprog, _ = subst_rec cutprob s progctx in
       let subst_where {where_id; where_path; where_orig; where_nctx;
                        where_prob; where_arity; where_term;
                        where_type; where_splitting } =
         let nsubst, where_nctx = subst_rec_named s where_nctx in
         let where_arity = mapping_constr evd subst where_arity in
         let where_term = mapping_constr evd subst where_term in
         let where_type = mapping_constr evd subst where_type in
         let where_splitting =
           map_split (fun t -> replace_vars nsubst t) where_splitting
         in
         {where_id; where_path; where_orig; where_nctx; where_prob;
          where_arity; where_term;
          where_type; where_splitting }
       in
       let where' = List.map subst_where where in
       Compute (lhs', where', mapping_constr evd substprog ty,
                mapping_rhs evd substprog c)
	       
    | Split (lhs, n, ty, cs) -> 
       let subst, lhs' = subst_rec cutprob s lhs in
       let n' = destRel evd (mapping_constr evd subst (mkRel n)) in
       Split (lhs', n', mapping_constr evd subst ty,
	      Array.map (Option.map (aux cutprob s path)) cs)

    | Mapping (lhs, c) ->
       let subst, lhs' = subst_rec cutprob s lhs in
       Mapping (lhs', aux cutprob s path c)
	       
    | RecValid (id, c) ->
       RecValid (id, aux cutprob s path c)
		
    | Refined (lhs, info, sp) -> 
       let (id, c, cty), ty, arg, ev, (fev, args), revctx, newprob, newty =
	 info.refined_obj, info.refined_rettyp,
	 info.refined_arg, info.refined_ex, info.refined_app,
	 info.refined_revctx, info.refined_newprob, info.refined_newty
       in
       let subst, lhs' = subst_rec cutprob s lhs in
       let cutprob ctx' = 
	 let pats, cutctx', _, _ =
	   (* From Γ |- ps, prec, ps' : Δ, rec, Δ', build
	       Γ |- ps, ps' : Δ, Δ' *)
	   List.fold_right (fun d (pats, ctx', i, subs) ->
               let (n, b, t) = to_tuple d in
	       match n with
	       | Name n when List.mem_assoc n s ->
		  let term = List.assoc n s in
		  let term = map_proto term t in
		  (pats, ctx', pred i, term :: subs)
	       | _ ->
                  let decl = of_tuple (n, Option.map (substl subs) b, substl subs t) in
		  (i :: pats, decl :: ctx', 
		   pred i, mkRel 1 :: List.map (lift 1) subs))
		      ctx' ([], [], List.length ctx', [])
 	 in (ctx', List.map (fun i -> PRel i) pats, cutctx')
       in
       let _, revctx' = subst_rec (cutprob (pi3 revctx)) s revctx in
       let cutnewprob = cutprob (pi3 newprob) in
       let subst', newprob' = subst_rec cutnewprob s newprob in
       let _, newprob_to_prob' = 
	 subst_rec (cutprob (pi3 info.refined_newprob_to_lhs)) s info.refined_newprob_to_lhs in
       let ev' = if Option.has_some comprecarg then new_untyped_evar () else ev in
       let path' = ev' :: path in
       let app', arg' =
	 if Option.has_some comprecarg then
	   let refarg = ref 0 in
  	   let args' =
             CList.fold_left_i
	       (fun i acc c -> 
		 if i == arg then (refarg := List.length acc);
                 if isRel evd c then
                   let d = List.nth (pi1 lhs) (pred (destRel evd c)) in
		   if List.mem_assoc (Nameops.out_name (get_name d)) s then acc
                   else (mapping_constr evd subst c) :: acc
                 else (mapping_constr evd subst c) :: acc) 0 [] args
           in
           let secvars =
             let named_context = Environ.named_context env in
               List.map (fun decl ->
                 let id = Context.Named.Declaration.get_id decl in
                 EConstr.mkVar id) named_context
           in
           let secvars = Array.of_list secvars in
	    (mkEvar (ev', secvars), List.rev args'), !refarg
	 else 
           let first, last = CList.chop (List.length s) (List.map (mapping_constr evd subst) args) in
           (applistc (mapping_constr evd subst fev) first, last), arg - List.length s
           (* FIXME , needs substituted position too *)
       in
       let info =
         { refined_obj = (id, mapping_constr evd subst c, mapping_constr evd subst cty);
           refined_rettyp = mapping_constr evd subst ty;
	   refined_arg = arg';
	   refined_path = path';
	   refined_ex = ev';
	   refined_app = app';
	   refined_revctx = revctx';
	   refined_newprob = newprob';
	   refined_newprob_to_lhs = newprob_to_prob';
           refined_newty = mapping_constr evd subst' newty }
       in Refined (lhs', info, aux cutnewprob s path' sp)

    | Valid (lhs, x, y, w, u, cs) -> 
       let subst, lhs' = subst_rec cutprob s lhs in
       Valid (lhs', x, y, w, u, 
	      List.map (fun (g, l, subst, invsubst, sp) -> (g, l, subst, invsubst, aux cutprob s path sp)) cs)
  in aux prob s [] split

let update_split env evd is_rec f prob recs split =
  let where_map = ref Evar.Map.empty in
  match is_rec with
  | Some (Syntax.Structural _) -> subst_rec_split env !evd f false None prob recs split, !where_map
  | Some (Logical r) -> 
    let proj = match r with
      | LogicalDirect (_, id) -> mkVar id
      | LogicalProj r -> mkConst r.comp_proj
    in
    let split' = subst_comp_proj_split !evd f proj split in
    let rec aux env f = function
      | RecValid (id, Valid (ctx, ty, args, tac, view, 
			    [goal, args', newprob, invsubst, rest])) ->
        let recarg = match r with
          | LogicalDirect _ -> Some (-1)
          | LogicalProj r -> Some r.comp_recarg
        in
	let rest = aux env f (subst_rec_split env !evd f false recarg
                     newprob [(id, f)] rest) in
	 (match invsubst with
	  | Some s -> Mapping (s, rest)
	  | None -> rest)
      | Mapping (lhs, s) -> Mapping (lhs, aux env f s)
      | Split (lhs, y, z, cs) -> Split (lhs, y, z, Array.map (Option.map (aux env f)) cs)
      | RecValid (id, c) -> RecValid (id, aux env f c)
      | Valid (lhs, y, z, w, u, cs) ->
	Valid (lhs, y, z, w, u, 
	       List.map (fun (gl, cl, subst, invs, s) -> (gl, cl, subst, invs, aux env f s)) cs)
      | Refined (lhs, info, s) -> Refined (lhs, info, aux env f s)
      | Compute (lhs, wheres, p, q) -> 
         let subst_where w = 
           let env = push_named_context w.where_nctx env in
           let evm, ev = (* Why create an evar here ? *)
             Equations_common.new_evar env !evd w.where_type
           in
           let () = evd := evm in
           let term' = substl (List.map (fun x -> mkVar (get_id x)) w.where_nctx) w.where_term in
           let evk = fst (destEvar !evd ev) in
           let split' = aux env term' w.where_splitting in
           let id = Nameops.add_suffix w.where_id "_unfold_eq" in
           let () = where_map := Evar.Map.add evk (term', id, split') !where_map in
           (* msg_debug (str"At where in update_split, calling recursively with term" ++ *)
           (*              pr_constr w.where_term ++ str " associated to " ++ int (Evar.repr evk)); *)
           { w with where_term = ev;
                    where_path = evk :: List.tl w.where_path;
                    where_splitting = split' }
         in
         Compute (lhs, List.map subst_where wheres, p, q)
    in
    let split' = aux env f split' in
    split', !where_map
  | _ -> split, !where_map

let computations env evd alias refine eqninfo =
  let { equations_prob = prob;
        equations_where_map = wheremap;
        equations_f = f;
        equations_split = split } = eqninfo in
  let rec computations env prob f alias refine = function
  | Compute (lhs, where, ty, c) ->
     let where_comp w =
       (** Where term is in lhs, now move relative references to
              lhs to named ones, this puts it in nctx. *)
       let rctx, inst = rel_of_named_context w.where_nctx in
       let instc = List.map mkVar inst in
       (** nctx; lhs |- nterm *)
       let nterm = substl instc w.where_term in
       let alias =
         try
         let (f, id, s) = Evar.Map.find (List.hd w.where_path) wheremap in
         let args = match_arguments evd (arguments evd nterm) (arguments evd f) in
         Some ((f, args), id, s)
         with Not_found -> None
       in
       let env' = push_named_context w.where_nctx env in
       let comps = computations env' w.where_prob nterm None (Regular,false) w.where_splitting in
       let gencomp (ctx, fl, alias, pats, ty, f, b, c, l) =
         (** ctx' = rctx ++ lhs is a dB context *)
         let lift, ctx' = replace_vars_context inst ctx in
         let ctx' = ctx' @ rctx in
         let alias' =
           match alias with
           | Some (hd, id, s) -> Some (substn_vars lift inst hd, id, s)
           | None -> None
         in
         ctx', substn_vars lift inst fl, alias',
         pats, substn_vars lift inst ty,
         substn_vars lift inst f, b,
         map_rhs (substn_vars lift inst) (fun x -> x) c, l
       in
       let rest = List.map gencomp comps in
       let lift, ctx' = replace_vars_context inst (pi1 w.where_prob) in
       let ctx' = ctx' @ rctx in
       (** ctx' is a dB context for nctx + where_prob *)
       let hd = substn_vars lift inst nterm in
       let args =
         let rec aux i a =
           match a with
           | [] -> []
           | hd :: tl -> if isRel evd hd then i :: aux (succ i) tl
                         else aux (succ i) tl
         in aux 0 (Array.to_list (arguments evd hd))
       in
       let arity = substn_vars lift inst w.where_arity in
       ((hd, args), alias, w.where_orig, ctx', arity,
        List.rev_map pat_constr (pi2 w.where_prob) (*?*),
        [] (*?*), rest)
     in
     let wheres = List.map where_comp where in
     let ctx = compose_subst env ~sigma:evd lhs prob in
     let inst = where_instance where in
     let ninst = List.map (fun n -> Nameops.out_name (get_name n)) (pi1 ctx) in
     let inst = List.map (fun c -> substn_vars 1 ninst c) inst in
     let c' = map_rhs (fun c -> Reductionops.nf_beta Evd.empty (substl inst c)) (fun x -> x) c in
     let patsconstrs = List.rev_map pat_constr (pi2 ctx) in
     [pi1 ctx, f, alias, patsconstrs, substl inst ty, f, (Where, snd refine), c', Some wheres]

  | Split (_, _, _, cs) -> Array.fold_left (fun acc c ->
	                   match c with None -> acc | Some c ->
	                                               acc @ computations env prob f alias refine c) [] cs

  | Mapping (lhs, c) ->
     let _newprob = compose_subst env ~sigma:evd prob lhs in
     computations env prob f alias refine c

  | RecValid (id, cs) -> computations env prob f alias (fst refine, false) cs

  | Refined (lhs, info, cs) ->
     let (id, c, t) = info.refined_obj in
     let (ctx', pats', _ as s) = compose_subst env ~sigma:evd lhs prob in
     let patsconstrs = List.rev_map pat_constr pats' in
     let refinedpats = List.rev_map pat_constr
	                            (pi2 (compose_subst env ~sigma:evd info.refined_newprob_to_lhs s))
     in
     let filter = [Array.length (arguments evd (fst info.refined_app))] in
     [pi1 lhs, f, alias, patsconstrs, info.refined_rettyp, f, (Refine, true),
      RProgram (applist info.refined_app),
      Some [(fst (info.refined_app), filter), None, info.refined_path, pi1 info.refined_newprob,
	    info.refined_newty, refinedpats,
            [mapping_constr evd info.refined_newprob_to_lhs c, info.refined_arg],
	    computations env info.refined_newprob (fst info.refined_app) None (Regular, true) cs]]

  | Valid ((ctx,pats,del), _, _, _, _, cs) ->
     List.fold_left (fun acc (_, _, subst, invsubst, c) ->
     let subst = compose_subst env ~sigma:evd subst prob in
     acc @ computations env subst f alias (fst refine,false) c) [] cs
  in computations env prob (of_constr f) alias refine split

let constr_of_global_univ gr u =
  let open Globnames in
  match gr with
  | ConstRef c -> mkConstU (c, u)
  | IndRef i -> mkIndU (i, u)
  | ConstructRef c -> mkConstructU (c, u)
  | VarRef id -> mkVar id

let declare_funelim info env evd is_rec protos progs
                    ind_stmts all_stmts sign app subst inds kn comb
                    indgr ectx =
  let id = Id.of_string info.base_id in
  let leninds = List.length inds in
  let elim =
    if leninds > 1 || get_sort () != InProp then comb
    else
      let elimid = Nameops.add_suffix id "_ind_ind" in
      Smartlocate.global_with_alias (reference_of_id elimid)
  in
  let elimc, elimty =
    let elimty, uctx = Global.type_of_global_in_context (Global.env ()) elim in
    let () = evd := Evd.from_env (Global.env ()) in
    if is_polymorphic info then
      let _fty, fctx = Global.type_of_global_in_context (Global.env ()) info.term_id in
      let fctx = Univ.ContextSet.of_context fctx in
      let elimctx = Univ.ContextSet.of_context uctx in
      (** They share universes in general *)
      let fullctx = Univ.ContextSet.union fctx elimctx in
      let () = evd := Evd.merge_context_set Evd.univ_flexible !evd fullctx in
      let u = Univ.UContext.instance uctx in
      let elimty = subst_instance_constr u elimty in
      let elimc = constr_of_global_univ elim (EInstance.make u) in
      (** evd contains the universes of the elim and the function, which
          correspond to the universes in ind_stmts, all_stmts etc...
          This is a bit dirty but avoids keeping track of a universe substitution
          and applying it to all the derived datastructures. *)
      elimc, elimty
    else (* If not polymorphic, we just use the global environment's universes for f and elim *)
      (let elimc = constr_of_global_univ elim EInstance.empty in
       elimc, elimty)
  in
  let nargs, newty =
    compute_elim_type env evd is_rec protos kn leninds ind_stmts all_stmts
                      sign app (of_constr elimty)
  in
  let hookelim _ elimgr _ =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let f_gr = Nametab.locate (Libnames.qualid_of_ident id) in
    let evd, f = new_global evd f_gr in
    let evd, elimcgr = new_global evd elimgr in
    let evd, cl = functional_elimination_class evd in
    let args_of_elim = coq_nat_of_int nargs in
    let args = [Retyping.get_type_of env evd f; f;
		Retyping.get_type_of env evd elimcgr;
                of_constr args_of_elim; elimcgr]
    in
    let instid = Nameops.add_prefix "FunctionalElimination_" id in
    let poly = is_polymorphic info in
    ignore(Equations_common.declare_instance instid poly evd [] cl args)
  in
  let tactic = ind_elim_tac elimc leninds (List.length progs) info indgr in
  let _ = e_type_of (Global.env ()) evd newty in
  ignore(Obligations.add_definition (Nameops.add_suffix id "_elim")
	                            ~tactic ~hook:(Lemmas.mk_hook hookelim) ~kind:info.decl_kind
                                    (to_constr !evd newty) (Evd.evar_universe_context !evd) [||])

let mkConj evd sort x y =
  let prod =
    if sort == InProp then
      e_new_global evd (Lazy.force Equations_common.prop_logic.logic_product)
    else
      e_new_global evd (Lazy.force Equations_common.type_logic.logic_product)
  in
    mkApp (prod, [| x; y |])

let declare_funind info alias env evd is_rec protos progs
                   ind_stmts all_stmts sign inds kn comb f split ind =
  let poly = is_polymorphic info.term_info in
  let id = Id.of_string info.term_info.base_id in
  let indid = Nameops.add_suffix id "_ind_fun" in
  let args = Termops.rel_list 0 (List.length sign) in
  let f, split, unfsplit =
    match alias with
    | Some (f, _, recsplit) -> f, recsplit, Some split
    | None -> f, split, None
  in
  let app = applist (f, args) in
  let statement =
    let stmt (i, ((f,_), alias, _, sign, ar, _, _, (nodek, cut)), _) =
      if not (regular_or_nested nodek) then None else
      let f, split, unfsplit =
        match alias with
        | Some ((f,_), _, recsplit) -> f, recsplit, Some split
        | None -> f, split, None
      in
      let args = extended_rel_list 0 sign in
      let app = applist (f, args) in
      let ind = Nameops.add_suffix (Id.of_string info.term_info.base_id)
                                   ("_ind" ^ if i == 0 then "" else "_" ^ string_of_int i) in
      let indt = e_new_global evd (global_reference ind) in
      Some (it_mkProd_or_subst (applist (indt, args @ [app])) sign)
    in
    match ind_stmts with
    | [] -> assert false
    | [hd] -> Option.get (stmt hd)
    | hd :: tl ->
       let l, last =
         let rec aux l =
           let last, l = CList.sep_last l in
           match stmt last with
           | None -> aux l
           | Some t -> t, l
         in aux ind_stmts
       in
       List.fold_right (fun x acc -> match stmt x with
                                     | Some t -> mkConj evd InProp t acc
                                     | None -> acc) last l
  in
  let hookind subst indgr ectx =
    let env = Global.env () in (* refresh *)
    Hints.add_hints false [info.term_info.base_id]
	            (Hints.HintsImmediateEntry [Hints.PathAny, poly, Hints.IsGlobRef indgr]);
    let () = declare_funelim info.term_info env evd is_rec protos progs
                             ind_stmts all_stmts sign app subst inds kn comb indgr ectx in
    let evd = Evd.from_env env in
    let f_gr = Nametab.locate (Libnames.qualid_of_ident id) in
    let evd, f = new_global evd f_gr in
    let evd, indcgr = new_global evd indgr in
    let evd, cl = functional_induction_class evd in
    let args = [Retyping.get_type_of env evd f; f;
	        Retyping.get_type_of env evd indcgr; indcgr]
    in
    let instid = Nameops.add_prefix "FunctionalInduction_" id in
    ignore(Equations_common.declare_instance instid poly evd [] cl args);
    (** If desired the definitions should be made transparent again. *)
    if !Equations_common.equations_transparent then
      (Global.set_strategy (ConstKey (fst (destConst evd f))) Conv_oracle.transparent;
        match alias with
        | None -> ()
        | Some (f, _, _) -> Global.set_strategy (ConstKey (fst (destConst evd f))) Conv_oracle.transparent)
  in
  let ctx = Evd.evar_universe_context (if poly then !evd else Evd.from_env (Global.env ())) in
  try ignore(Obligations.add_definition
             ~hook:(Lemmas.mk_hook hookind)
             ~kind:info.term_info.decl_kind
             indid (to_constr !evd statement)
             ~tactic:(ind_fun_tac is_rec (to_constr !evd f) info id split unfsplit progs) ctx [||])
  with e ->
    Feedback.msg_warning Pp.(str "Induction principle could not be proved automatically: " ++ fnl () ++
		             CErrors.print e)


let level_of_context env evd ctx acc =
  let _, lev =
    List.fold_right (fun decl (env, lev) ->
        let s = Retyping.get_sort_of env evd (get_type decl) in
        (push_rel decl env, Univ.sup (Sorts.univ_of_sort s) lev))
                    ctx (env,acc)
  in lev

let build_equations with_ind env evd ?(alias:(constr * Names.Id.t * splitting) option) progs =
  let p, prog, eqninfo = List.hd progs in
  let { equations_id = id;
        equations_where_map = wheremap;
        equations_f = f;
        equations_prob = prob;
        equations_split = split } = eqninfo in
  let info = prog.program_split_info in
  let sign = p.program_sign in
  let is_rec = p.program_rec in
  let cst = prog.program_cst in
  let comps =
    let fn p = computations env evd alias (kind_of_prog p,false) in
    List.map (fun (p, prog, eqninfo) -> p, eqninfo, fn p eqninfo) progs
  in
  let rec flatten_comp (ctx, fl, flalias, pats, ty, f, refine, c, rest) =
    let rest = match rest with
      | None -> []
      | Some l ->
         CList.map_append (fun (f, alias, path, ctx, ty, pats, newargs, rest) ->
	  let nextlevel, rest = flatten_comps rest in
	    ((f, alias, path, ctx, ty, pats, newargs, refine), nextlevel) :: rest) l
    in (ctx, fl, flalias, pats, ty, f, refine, c), rest
  and flatten_comps r =
    List.fold_right (fun cmp (acc, rest) -> 
      let stmt, rest' = flatten_comp cmp in
	(stmt :: acc, rest' @ rest)) r ([], [])
  in
  let flatten_top_comps (p, eqninfo, one_comps) acc =
    let (top, rest) = flatten_comps one_comps in
    let alias = match alias with Some (f, id, x) -> Some ((f, []), id, x) | None -> None in
    let topcomp = (((of_constr eqninfo.equations_f,[]), alias, [],
                    p.program_sign, p.program_arity,
                    List.rev_map pat_constr (pi2 eqninfo.equations_prob), [],
                    (kind_of_prog p,false)), top) in
    topcomp :: (rest @ acc)
  in
  let comps = List.fold_right flatten_top_comps comps [] in
  let protos = List.map fst comps in
  let lenprotos = List.length protos in
  let protos = 
    CList.map_i (fun i ((f',filterf'), alias, path, sign, arity, pats, args, (refine, cut)) ->
      let f' = Termops.strip_outer_cast evd f' in
      let alias =
        match alias with
        | None -> None
        | Some (f, _, _) -> Some f
      in
      ((f',filterf'), alias, lenprotos - i, sign, to_constr evd arity))
      1 protos
  in
  let evd = ref evd in    
  let poly = is_polymorphic info in
  let statement i filter (ctx, fl, flalias, pats, ty, f', (refine, cut), c) =
    let hd, unf = match flalias with
      | Some (f', unf, _) -> f', Equality.rewriteLR (constr_of_ident unf)
      | None -> fl,
               if eq_constr !evd fl (of_constr f) then of82 (unfold_constr !evd (of_constr f))
               else Tacticals.New.tclIDTAC
    in
    let comp = applistc hd pats in
    let body =
      let b = match c with
	| RProgram c ->
	    mkEq env evd ty comp (Reductionops.nf_beta !evd c)
	| REmpty i ->
	   mkApp (coq_ImpossibleCall evd, [| ty; comp |])
      in
      let body = it_mkProd_or_LetIn b ctx in
      (* msg_debug (str"Typing equation " ++ pr_constr_env env !evd c); *)
      let _ = Typing.e_type_of env evd body in
      body
    in
    let cstr = 
      match c with
      | RProgram c ->
	  let len = List.length ctx in
	  let hyps, hypslen, c' =
            abstract_rec_calls !evd is_rec len protos (Reductionops.nf_beta Evd.empty c)
          in
          let head =
            let f = mkRel (len + (lenprotos - i) + hypslen) in
            if cut then f 
            else 
              let fn, args = decompose_app !evd (Termops.strip_outer_cast !evd fl) in
              applistc f (filter_arguments filter (lift_constrs hypslen args))
          in
          let ty = 
            it_mkProd_or_clear !evd
              (it_mkProd_or_clean
		 (applistc head (lift_constrs hypslen pats @ [c']))
		 hyps) ctx
          in Some ty
      | REmpty i -> None
    in (refine, unf, body, cstr)
  in
  let statements i ((f', alias, path, sign, arity, pats, args, refine as fs), c) =
    let fs, filter =
      match alias with
      | Some (f', unf, split) ->
	 (f', None, path, sign, arity, pats, args, refine), snd f'
      | None -> fs, snd f'
    in fs, List.map (statement i filter) c in
  let stmts = CList.map_i statements 0 comps in
  let ind_stmts = CList.map_i 
    (fun i (f, c) -> i, f, CList.map_i (fun j x -> j, x) 1 c) 0 stmts
  in
  let all_stmts = List.concat (List.map (fun (f, c) -> c) stmts) in
  let fnind_map = ref PathMap.empty in
  let declare_one_ind (i, (f, alias, path, sign, arity, pats, refs, refine), stmts) =
    let indid = Nameops.add_suffix id (if i == 0 then "_ind" else ("_ind_" ^ string_of_int i)) in
    let indapp = List.rev_map (fun x -> Constr.mkVar (Nameops.out_name (get_name x))) sign in
    let () = fnind_map := PathMap.add path (indid,indapp) !fnind_map in
    let constructors = CList.map_filter (fun (_, (_, _, _, n)) -> Option.map (to_constr !evd) n) stmts in
    let consnames = CList.map_filter (fun (i, (r, _, _, n)) ->
      Option.map (fun _ -> 
        let suff = (if r != Refine then "_equation_" else "_refinement_") ^ string_of_int i in
	  Nameops.add_suffix indid suff) n) stmts
    in
    let ind_sort =
      if get_sort () == InProp then
        (** Define graph impredicatively *)
        mkProp
      else (** Compute sort as max of products *)
        let ctx = (of_tuple (Anonymous, None, arity) :: sign) in
        let signlev = level_of_context env !evd ctx Univ.type0m_univ in
        mkSort (Sorts.sort_of_univ signlev)
    in
      Entries.{ mind_entry_typename = indid;
        mind_entry_arity = to_constr !evd (it_mkProd_or_LetIn (mkProd (Anonymous, arity, ind_sort)) sign);
	mind_entry_consnames = consnames;    
	mind_entry_lc = constructors;
	mind_entry_template = false }
  in
  let declare_ind () =
    let inds = List.map declare_one_ind ind_stmts in
    let uctx = snd (Evd.universe_context !evd) in
    let inductive =
      Entries.{ mind_entry_record = None;
                mind_entry_universes = if poly then Polymorphic_ind_entry uctx
                                       else Monomorphic_ind_entry uctx;
                mind_entry_private = None;
                mind_entry_finite = Decl_kinds.Finite;
                mind_entry_params = []; (* (identifier * local_entry) list; *)
                mind_entry_inds = inds }
    in
    let () = Goptions.set_bool_option_value_gen (Some true) ["Elimination";"Schemes"] false in
    let kn = Command.declare_mutual_inductive_with_eliminations inductive [] [] in
    let () = Goptions.set_bool_option_value_gen (Some true) ["Elimination";"Schemes"] true in
    let kn, comb =
      let sort, suff = match get_sort () with
        | InProp -> Misctypes.GProp, "_ind"
        | InSet -> Misctypes.GSet, "_rec"
        | InType -> Misctypes.GType [], "_rect"
      in
      let mutual =
        (CList.map_i (fun i ind ->
             let suff = if List.length inds != 1 then "_mut" else suff in
             let id = (dummy_loc, Nameops.add_suffix ind.Entries.mind_entry_typename suff) in
             (id, false, (kn, i), sort)) 0 inds)
      in
      Indschemes.do_mutual_induction_scheme mutual;
      if List.length inds != 1 then
        let scheme = Nameops.add_suffix (Id.of_string info.base_id) "_ind_comb" in
        let mutual = List.map2 (fun (i, _, _, _) (_, (_, _, _, _, _, _, _, (kind, cut)), _) ->
                         i, regular_or_nested_rec kind) mutual ind_stmts in
        let () =
          Indschemes.do_combined_scheme
            (None, scheme)
            (CList.map_filter (fun (id, b) -> if b then Some id else None) mutual)
        in kn, Smartlocate.global_with_alias (reference_of_id scheme)
      else 
        let scheme = Nameops.add_suffix (Id.of_string info.base_id) ("_ind" ^ suff) in
        kn, Smartlocate.global_with_alias (reference_of_id scheme)
    in
    let ind =
      if poly then
        mkIndU ((kn,0), EInstance.make (Univ.UContext.instance uctx))
      else mkInd (kn,0)
    in
    let _ =
      List.iteri (fun i ind ->
	let constrs = 
	  CList.map_i (fun j _ -> Hints.empty_hint_info, poly, true, Hints.PathAny, 
	    Hints.IsGlobRef (Globnames.ConstructRef ((kn,i),j))) 1 ind.Entries.mind_entry_lc in
	  Hints.add_hints false [info.base_id] (Hints.HintsResolveEntry constrs))
	inds
    in
    let info = { term_info = info; pathmap = !fnind_map; wheremap } in
    declare_funind info alias env evd is_rec protos progs
                   ind_stmts all_stmts sign inds kn comb
                   (of_constr f) split ind
  in
  let () = evd := Evd.nf_constraints !evd in
  let () =
    if not poly then
      (** Declare the universe context necessary to typecheck the following
          definitions once and for all. *)
      (Declare.declare_universe_context false (Evd.universe_context_set !evd);
       evd := Evd.from_env (Global.env ()))
    else ()
  in
  let proof (j, f, stmts) =
    let eqns = Array.make (List.length stmts) false in
    let id = if j != 0 then Nameops.add_suffix id ("_helper_" ^ string_of_int j) else id in
    let proof (i, (r, unf, c, n)) =
      let ideq = Nameops.add_suffix id ("_equation_" ^ string_of_int i) in
      let hook subst gr _ = 
	if n != None then
	  Autorewrite.add_rew_rules info.base_id 
            [None, (Universes.fresh_global_instance (Global.env()) gr, true, None)]
	else (Typeclasses.declare_instance None true gr
	      (* Hints.add_hints false [info.base_id]  *)
	      (*                 (Hints.HintsExternEntry *)
              (*                  (Vernacexpr.{hint_priority = Some 0; hint_pattern = None}, *)
              (*                   impossible_call_tac (Globnames.ConstRef cst))) *));
	eqns.(pred i) <- true;
	if CArray.for_all (fun x -> x) eqns then (
	  (* From now on, we don't need the reduction behavior of the constant anymore *)
	  Typeclasses.set_typeclass_transparency (EvalConstRef cst) false false;
          (match alias with
           | Some (f, _, _) ->
              Global.set_strategy (ConstKey (fst (destConst !evd f))) Conv_oracle.Opaque
           | None -> ());
	  Global.set_strategy (ConstKey cst) Conv_oracle.Opaque;
	  if with_ind && succ j == List.length ind_stmts then declare_ind ())
      in
      let tac =
	(Tacticals.tclTHENLIST [to82 Tactics.intros; to82 unf;
                                to82 (solve_equation_tac (Globnames.ConstRef cst))])
      in
      let () =
        (** Refresh at each equation, accumulating known constraints. *)
        if not poly then evd := Evd.from_env (Global.env ())
        else ()
      in
      ignore(Obligations.add_definition
               ~kind:info.decl_kind
               ideq (to_constr !evd c)
               ~tactic:(of82 tac) ~hook:(Lemmas.mk_hook hook)
	       (Evd.evar_universe_context !evd) [||])
    in List.iter proof stmts
  in List.iter proof ind_stmts
