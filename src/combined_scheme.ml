open Equations_common

open CErrors
open Util
open Entries
open Term
open Constr
open Decl_kinds
open Declare
open Termops

let list_split_rev_at index l =
  let rec aux i acc = function
      hd :: tl when Int.equal i index -> acc, tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "List.split_when: Invalid argument"
  in aux 0 [] l

let fold_left' f = function
    [] -> invalid_arg "fold_left'"
  | hd :: tl -> List.fold_left f hd tl

let build_combined_scheme env schemes =
  let sigma = Evd.from_env env in
  let sigma, defs = CList.fold_left_map (fun sigma cst ->
    let sigma, c = Evd.fresh_constant_instance env sigma cst in
    sigma, (c, Typeops.type_of_constant_in env c)) sigma schemes in
  let find_inductive ty =
    let (ctx, arity) = Term.decompose_prod ty in
    let (_, last) = List.hd ctx in
      match Constr.kind last with
        | App (ind, args) ->
            let ind = destInd ind in
            let (_,spec) = Inductive.lookup_mind_specif env (fst ind) in
              ctx, ind, spec.Declarations.mind_nrealargs
        | _ -> ctx, destInd last, 0
  in
  let (c, t) = List.hd defs in
  let ctx, ind, nargs = find_inductive t in
  (* We check if ALL the predicates are in Prop, if so we use propositional
     conjunction '/\', otherwise we use the simple product '*'.
  *)
  let inprop =
    let inprop (_,t) =
      Retyping.get_sort_family_of env sigma (EConstr.of_constr t)
      == Sorts.InProp
    in
    List.for_all inprop defs
  in
  let mk_and, mk_conj =
    if inprop
    then (logic_conj, logic_conj_intro)
    else (logic_product, logic_pair)
  in
  (* Number of clauses, including the predicates quantification *)
  let prods = Termops.nb_prod sigma (EConstr.of_constr t) - (nargs + 1) in
  let sigma, coqand  = get_fresh sigma mk_and in
  let sigma, coqconj = get_fresh sigma mk_conj in
  let relargs = Termops.rel_vect 0 prods in
  let concls = List.rev_map
    (fun (cst, t) ->
      Constr.mkApp(Constr.mkConstU cst, relargs),
      snd (decompose_prod_n prods t)) defs in
  let concl_bod, concl_typ =
    fold_left'
      (fun (accb, acct) (cst, x) ->
        mkApp (EConstr.to_constr sigma coqconj, [| x; acct; cst; accb |]),
        mkApp (EConstr.to_constr sigma coqand, [| x; acct |])) concls
  in
  let ctx, _ =
    list_split_rev_at prods
      (List.rev_map (fun (x, y) -> Context.Rel.Declaration.LocalAssum (x, y)) ctx) in
  let typ = List.fold_left (fun d c -> Term.mkProd_wo_LetIn c d) concl_typ ctx in
  let body = it_mkLambda_or_LetIn concl_bod ctx in
  let sigma = Typing.check env sigma (EConstr.of_constr body) (EConstr.of_constr typ) in
  (sigma, body, typ)

let define ~poly id internal ctx c t =
  let f = declare_constant ~internal in
  let univs =
    if poly
    then Polymorphic_const_entry (Evd.to_universe_context ctx)
    else Monomorphic_const_entry (Evd.universe_context_set ctx)
  in
  let kn = f id
    (DefinitionEntry
      { const_entry_body = c;
        const_entry_secctx = None;
        const_entry_type = t;
        const_entry_universes = univs;
        const_entry_opaque = false;
        const_entry_inline_code = false;
        const_entry_feedback = None;
      },
      Decl_kinds.IsDefinition Scheme) in
  definition_message id;
  kn

let do_combined_scheme name schemes =
  let open CAst in
  let csts =
    List.map (fun {CAst.loc;v} ->
        let qualid = Libnames.qualid_of_ident v in
        try Nametab.locate_constant qualid
        with Not_found -> CErrors.user_err ?loc Pp.(Libnames.pr_qualid qualid ++ str " is not declared."))
      schemes
  in
  let sigma,body,typ = build_combined_scheme (Global.env ()) csts in
  let proof_output = Future.from_val ((body,Univ.ContextSet.empty),Safe_typing.empty_private_constants) in
  (* It is possible for the constants to have different universe
     polymorphism from each other, however that is only when the user
     manually defined at least one of them (as Scheme would pick the
     polymorphism of the inductive block). In that case if they want
     some other polymorphism they can also manually define the
     combined scheme. *)
  let poly = Global.is_polymorphic (Names.GlobRef.ConstRef (List.hd csts)) in
  ignore (define ~poly name.v UserIndividualRequest sigma proof_output (Some typ));
  fixpoint_message None [name.v]
