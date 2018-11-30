open Pp
open EConstr
(* ========== Coq references ========= *)
(* This section should change a lot when we approach an actual solution. *)

module type SIGMAREFS = sig
  val sigma : Names.inductive Lazy.t
  val sigmaI : Names.constructor Lazy.t
end

module type EQREFS = sig
  (* Equality type. *)
  val eq : Names.inductive Lazy.t
  val eq_refl : Names.constructor Lazy.t
  val eq_rect : Names.Constant.t Lazy.t
  val eq_rect_r : Names.Constant.t Lazy.t
  (* Decidable equality typeclass. *)
  val eq_dec : Names.Constant.t Lazy.t
  (* Logic types. *)
  val zero : Names.inductive Lazy.t
  val one : Names.inductive Lazy.t
  val one_val : Names.constructor Lazy.t
  val one_ind_dep : Names.Constant.t Lazy.t
  val zero_ind : Names.Constant.t Lazy.t
  val zero_ind_dep : Names.Constant.t Lazy.t
  (* NoConfusion. *)
  val noConfusion : Names.inductive Lazy.t
  val apply_noConfusion : Names.Constant.t Lazy.t
  val simplify_ind_pack : Names.Constant.t Lazy.t
  val simplify_ind_pack_inv : Names.Constant.t Lazy.t
  val opaque_ind_pack_eq_inv : Names.Constant.t Lazy.t
  (* Simplification of dependent pairs. *)
  val simpl_sigma : Names.Constant.t Lazy.t
  val simpl_sigma_dep : Names.Constant.t Lazy.t
  val simpl_sigma_dep_dep : Names.Constant.t Lazy.t
  val pack_sigma_eq : Names.Constant.t Lazy.t
  (* Deletion using K. *)
  val simpl_K : Names.Constant.t Lazy.t
  val simpl_K_dec : Names.Constant.t Lazy.t
  (* Solution lemmas. *)
  val solution_left : Names.Constant.t Lazy.t
  val solution_left_dep : Names.Constant.t Lazy.t
  val solution_right : Names.Constant.t Lazy.t
  val solution_right_dep : Names.Constant.t Lazy.t
end

module RefsHelper = struct
  let init_gr s = Lazy.force s
  let init_inductive s = lazy (Globnames.destIndRef (init_gr s))
  let init_constructor s = lazy (Globnames.destConstructRef (init_gr s))
  let init_constant s = lazy (Globnames.destConstRef (init_gr s))
end

(* This should be parametrizable by the user. *)
module EqRefs : EQREFS = struct
  include RefsHelper

  open Equations_common

  let eq = init_inductive logic_eq_type
  let eq_refl = init_constructor logic_eq_refl
  let eq_rect = init_constant logic_eq_case
  let eq_rect_r = init_constant logic_eq_elim
  let eq_dec = init_constant logic_eqdec_class
  let zero = init_inductive logic_bot
  let one = init_inductive logic_top
  let one_val = init_constructor logic_top_intro
  let one_ind_dep = init_constant logic_top_elim
  let zero_ind = init_constant logic_bot_case
  let zero_ind_dep = init_constant logic_bot_elim

  let noConfusion = init_inductive coq_noconfusion_class

  let init_depelim s = init_constant (find_global ("depelim." ^ s))

  let apply_noConfusion = init_depelim "apply_noConfusion"
  let simplify_ind_pack = init_depelim "simplify_ind_pack"
  let simplify_ind_pack_inv = init_depelim "simplify_ind_pack_inv"
  let opaque_ind_pack_eq_inv = init_depelim "opaque_ind_pack_eq_inv"
  let simpl_sigma = init_depelim "simpl_sigma"
  let simpl_sigma_dep = init_depelim "simpl_sigma_dep"
  let simpl_sigma_dep_dep = init_depelim "simpl_sigma_dep_dep"
  let pack_sigma_eq = init_depelim "pack_sigma_eq"
  let simpl_K = init_depelim "simpl_K"
  let simpl_K_dec = init_depelim "simpl_K_dec"
  let solution_left = init_depelim "solution_left"
  let solution_left_dep = init_depelim "solution_left_dep"
  let solution_right = init_depelim "solution_right"
  let solution_right_dep = init_depelim "solution_right_dep"
end

(* This should not. *)
module SigmaRefs : SIGMAREFS = struct
  include RefsHelper

  let sigma = init_inductive Equations_common.coq_sigma
  let sigmaI = init_constructor Equations_common.coq_sigmaI
end

(* From the references, we can build terms. *)

type constr_gen = Evd.evar_map ref -> EConstr.constr

module type BUILDER = sig
  val sigma : constr_gen
  val sigmaI : constr_gen
  val eq : constr_gen
  val eq_refl : constr_gen
  val eq_dec : constr_gen
  val zero : constr_gen
  val one : constr_gen
  val one_val : constr_gen
  val one_ind_dep : constr_gen
  val zero_ind : constr_gen
  val zero_ind_dep : constr_gen
  val noConfusion : constr_gen
  val apply_noConfusion : constr_gen
  val simplify_ind_pack : constr_gen
  val simplify_ind_pack_inv : constr_gen
  val simpl_sigma : constr_gen
  val simpl_sigma_dep : constr_gen
  val simpl_sigma_dep_dep : constr_gen
  val simpl_K : constr_gen
  val simpl_K_dec : constr_gen
  val solution_left : constr_gen
  val solution_left_dep : constr_gen
  val solution_right : constr_gen
  val solution_right_dep : constr_gen
end

module BuilderHelper = struct
  let gen_from_inductive ind = fun evd ->
    let glob = Globnames.IndRef (Lazy.force ind) in
    Equations_common.e_new_global evd glob
  let gen_from_constant cst = fun evd ->
    let glob = Globnames.ConstRef (Lazy.force cst) in
    Equations_common.e_new_global evd glob
  let gen_from_constructor constr = fun evd ->
    let glob = Globnames.ConstructRef (Lazy.force constr) in
    Equations_common.e_new_global evd glob
end

module BuilderGen (SigmaRefs : SIGMAREFS) (EqRefs : EQREFS) : BUILDER = struct
  include BuilderHelper

  let sigma = gen_from_inductive SigmaRefs.sigma
  let sigmaI = gen_from_constructor SigmaRefs.sigmaI
  let eq = gen_from_inductive EqRefs.eq
  let eq_refl = gen_from_constructor EqRefs.eq_refl
  let eq_dec = gen_from_constant EqRefs.eq_dec
  let zero = gen_from_inductive EqRefs.zero
  let one = gen_from_inductive EqRefs.one
  let one_val = gen_from_constructor EqRefs.one_val
  let one_ind_dep = gen_from_constant EqRefs.one_ind_dep
  let zero_ind = gen_from_constant EqRefs.zero_ind
  let zero_ind_dep = gen_from_constant EqRefs.zero_ind_dep
  let noConfusion = gen_from_inductive EqRefs.noConfusion
  let apply_noConfusion = gen_from_constant EqRefs.apply_noConfusion
  let simplify_ind_pack = gen_from_constant EqRefs.simplify_ind_pack
  let simplify_ind_pack_inv = gen_from_constant EqRefs.simplify_ind_pack_inv
  let simpl_sigma = gen_from_constant EqRefs.simpl_sigma
  let simpl_sigma_dep = gen_from_constant EqRefs.simpl_sigma_dep
  let simpl_sigma_dep_dep = gen_from_constant EqRefs.simpl_sigma_dep_dep
  let simpl_K = gen_from_constant EqRefs.simpl_K
  let simpl_K_dec = gen_from_constant EqRefs.simpl_K_dec
  let solution_left = gen_from_constant EqRefs.solution_left
  let solution_left_dep = gen_from_constant EqRefs.solution_left_dep
  let solution_right = gen_from_constant EqRefs.solution_right
  let solution_right_dep = gen_from_constant EqRefs.solution_right_dep
end

module Builder : BUILDER = BuilderGen(SigmaRefs)(EqRefs)

(* ========== Simplification ========== *)

(* Some types to define what is a simplification. *)
type direction = Left | Right

type simplification_step =
    Deletion of bool (* Force the use of K? *)
  | Solution of direction
  | NoConfusion of simplification_rules
  | NoConfusionOut (* Step for the inversion of [simplify_ind_pack]. *)
  | NoCycle (* TODO: NoCycle should probably take a direction too. *)
  | ElimTrue | ElimFalse
and simplification_rule =
    Step of simplification_step
  | Infer_one
  | Infer_direction
  | Infer_many
and simplification_rules = (Loc.t option * simplification_rule) list

type goal = rel_context * EConstr.types
type open_term = (goal * EConstr.existential) option * EConstr.constr

exception CannotSimplify of Pp.t

type simplification_fun = Environ.env -> Evd.evar_map ref -> goal ->
  open_term * Covering.context_map

(* Auxiliary functions. *)

(* Build a term with an evar out of [constr -> constr] function. *)
let build_term (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal)
  ((ctx', ty') : goal) (f : EConstr.constr -> EConstr.constr) : open_term =
  let tev =
    let env = push_rel_context ctx' env in
    Equations_common.evd_comb1 (Evarutil.new_evar env) evd ty'
  in
  let c = f tev in
  let env = push_rel_context ctx env in
  let _ = Equations_common.evd_comb1 (Typing.type_of env) evd c in
  let ev = EConstr.destEvar !evd tev in
    Some ((ctx', ty'), ev), c


let build_app_infer (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal)
  (ctx' : EConstr.rel_context) (f : Names.GlobRef.t)
  (args : EConstr.constr option list) : open_term =
  let tf, ty =
    match f with
    | Globnames.VarRef var -> assert false
    | Globnames.ConstRef cst ->
        let pcst = Equations_common.evd_comb1 (Evd.fresh_constant_instance env) evd cst in
        let tf = Constr.mkConstU pcst in
        let ty = Typeops.type_of_constant_in env pcst in
          tf, ty
    | Globnames.IndRef ind ->
        let pind = Equations_common.evd_comb1 (Evd.fresh_inductive_instance env) evd ind in
        let tf = Constr.mkIndU pind in
        let ty = Inductiveops.type_of_inductive env pind in
          tf, ty
    | Globnames.ConstructRef cstr ->
        let pcstr = Equations_common.evd_comb1 (Evd.fresh_constructor_instance env) evd cstr in
        let tf = Constr.mkConstructU pcstr in
        let ty = Inductiveops.type_of_constructor env pcstr in
          tf, ty
  in
  let rec aux ty args =
    match kind !evd ty, args with
    | Constr.Prod (_, t, c), (Some hd) :: tl -> aux (Vars.subst1 hd c) tl
    | Constr.Prod (_, t, _), None :: _ -> t
    | Constr.LetIn (_, b, _, c), args -> aux (Vars.subst1 b c) args
    | Constr.Cast (c, _, _), args -> aux c args
    | _, _ -> failwith "Unexpected mismatch."
  in
  let tf = of_constr tf in
  let ty = of_constr ty in
  let ty' = aux ty args in
  let ty' = Reductionops.whd_beta !evd ty' in
    build_term env evd (ctx, ty) (ctx', ty') begin fun c ->
      let targs = Array.of_list (CList.map (Option.default c) args) in
        EConstr.mkApp (tf, targs) end

let conv_fun = Evarconv.evar_conv_x TransparentState.full
let is_conv (env : Environ.env) (sigma : Evd.evar_map) (ctx : rel_context)
  (t1 : EConstr.t) (t2 : EConstr.t) : bool =
  let env = push_rel_context ctx env in
  match Reductionops.infer_conv env sigma t1 t2 with
  | Some _ -> true
  | None -> false

(* Build an open term by substituting the second term for the hole in the
 * first term. *)
let compose_term (env : Environ.env) (evd : Evd.evar_map ref)
  ((h1, c1) : open_term) ((h2, c2) : open_term) : open_term =
  match h1 with
  | Some ((ctx1, _), (ev1, _)) ->
      let ev1_info = Evd.find !evd ev1 in
      let ev1_ctx = Evd.evar_context ev1_info in
      (* Keep only the context corresponding to [ctx1]. *)
      let named_ctx1 = CList.firstn (List.length ctx1) ev1_ctx in
      (* Now keep only the names and make terms out of them. *)
      let subst_ctx1 = List.map (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        EConstr.mkVar id) named_ctx1 in
      (* Finally, substitute the rels in [c2] to get a valid term for [ev1]. *)
      let c2 = Vars.substl subst_ctx1 c2 in
      evd := Evd.define ev1 c2 !evd;
      evd := Evarsolve.check_evar_instance !evd ev1 c2 conv_fun;
      h2, c1
  | None -> assert false

let compose_res (env : Environ.env) (evd : Evd.evar_map ref)
  ((t1, s1) : open_term * Covering.context_map)
  ((t2, s2) : open_term * Covering.context_map) : open_term * Covering.context_map =
    let t = compose_term env evd t1 t2 in
    let s = Covering.compose_subst env ~sigma:!evd s2 s1 in
      t, s

let safe_fun (f : simplification_fun) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let (_, c), _ as res = f env evd (ctx, ty) in
  let env = push_rel_context ctx env in
  evd := Typing.check env !evd c ty;
  res

(* Applies [g] to the goal, then [f]. *)
let compose_fun (f : simplification_fun) (g : simplification_fun) :
  simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let (h1, _), _ as res1 = g env evd gl in
  match h1 with
  | Some (gl', _) ->
      let res2 = f env evd gl' in compose_res env evd res1 res2
  | None -> res1


let identity : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  build_term env evd gl gl (fun c -> c), Covering.id_subst (fst gl)

let while_fun (f : simplification_fun) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let rec aux env evd gl =
    match f env evd gl with
    | (Some (gl', _), _), _ as res1 ->
        begin try
          let evd' = ref !evd in
          let res2 = aux env evd' gl' in
          let res = compose_res env evd' res1 res2 in
            evd := !evd'; res
        with CannotSimplify _ -> res1 end
    | (None, _), _ as res1 -> res1
  in try
    aux env evd gl
  with CannotSimplify _ -> identity env evd gl

(* Check if a type is a given inductive. *)
let check_inductive sigma (ind : Names.inductive) : EConstr.types -> bool =
  is_global sigma (Globnames.IndRef ind)
(* Check if a term is a given constructor. *)
let check_construct sigma (constr : Names.constructor) : EConstr.constr -> bool =
  is_global sigma (Globnames.ConstructRef constr)
(* Check if a term is a given constant. *)
let check_constant sigma (cst : Names.Constant.t) : EConstr.constr -> bool =
  is_global sigma (Globnames.ConstRef cst)

(* Deconstruct the goal if it's a product. Otherwise, raise CannotSimplify. *)
let check_prod sigma (ty : EConstr.types) : Names.Name.t * EConstr.types * EConstr.types =
  let name, ty1, ty2 = try destProd sigma ty
    with Constr.DestKO -> raise (CannotSimplify (str "The goal is not a product."))
  in name, ty1, ty2

let check_letin sigma (ty : EConstr.types) : Names.Name.t * EConstr.types * EConstr.types * EConstr.types =
  let name, na, ty1, body = try destLetIn sigma ty
    with Constr.DestKO -> raise (CannotSimplify (str "The goal is not a let-in."))
  in name, na, ty1, body

(* Check that the given type is an equality, and some
 * additional constraints if specified. Raise CannotSimplify if it's not
 * the case. Otherwise, return its arguments *)
let check_equality env sigma ctx ?(equal_terms : bool = false)
  ?(var_left : bool = false) ?(var_right : bool = false) (ty : EConstr.types) :
    EConstr.types * EConstr.constr * EConstr.constr =
  let f, args = Equations_common.decompose_appvect sigma ty in
  if not (check_inductive sigma (Lazy.force EqRefs.eq) f) then
    raise (CannotSimplify (str
      "The first hypothesis in the goal is not an equality."));
  let tA = args.(0) in
  let tx, ty = args.(1), args.(2) in
  if equal_terms && not (is_conv env sigma ctx tx ty) then
    raise (CannotSimplify (str
      "The first hypothesis in the goal is not an equality \
       between identical terms."));
  if var_left && not (EConstr.isRel sigma tx) then
    raise (CannotSimplify (str
      "The left-hand side of the first hypothesis in the goal is \
       not a variable."));
  if var_right && not (EConstr.isRel sigma ty) then
    raise (CannotSimplify (str
      "The right-hand side of the first hypothesis in the goal is \
       not a variable."));
  tA, tx, ty

let decompose_sigma sigma (t : EConstr.constr) :
  (EConstr.types * EConstr.constr * EConstr.constr * EConstr.constr) option =
  let f, args = Equations_common.decompose_appvect sigma t in
  if check_construct sigma (Lazy.force SigmaRefs.sigmaI) f then
    Some (args.(0), args.(1), args.(2), args.(3))
  else None

let with_retry (f : simplification_fun) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  try
    (* Be careful with the [evar_map] management. *)
    let evd' = ref !evd in
    let res = f env evd' (ctx, ty) in
    evd := !evd'; res
  with CannotSimplify _ ->
    (*msg_info (str "Reduce!");*)
    let reduce c =
      let env = push_rel_context ctx env in
        Tacred.hnf_constr env !evd c
    in
    (* Try to head-reduce the goal and reapply f. *)
    let ty = reduce ty in
    (* We try to reduce further when the goal is a product. *)
    let ty = try
      let name, ty1, ty2 = destProd !evd ty in
      let ty1 = reduce ty1 in
      let ty = mkProd (name, ty1, ty2) in
      (* If the head is an equality, reduce it. *)
      try
        let name, ty1, ty2 = check_prod !evd ty in
        let tA, t1, t2 = check_equality env !evd ctx ty1 in
        let t1 = reduce t1 in
        let t2 = reduce t2 in
        let ty1 = EConstr.mkApp (Builder.eq evd, [| tA; t1; t2 |]) in
          EConstr.mkProd (name, ty1, ty2)
      with CannotSimplify _ -> ty
      with Constr.DestKO -> ty
    in
      f env evd (ctx, ty)

(* Simplification functions to handle each step. *)
(* Any of these can throw a CannotSimplify exception which explains why the
 * rule cannot apply. *)

(* This function is not accessible by the user for now. It is used to project
 * (if needed) the first component of an equality between sigmas. It will not
 * do anything if it fails. *)
let remove_one_sigma : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let _, t1, t2 = check_equality env !evd ctx ty1 in
  let f, args =
    match decompose_sigma !evd t1, decompose_sigma !evd t2 with
    | Some (tA, tB, tt, tp), Some (_, _, tu, tq) ->
        (* Determine the degree of dependency. *)
        if Vars.noccurn !evd 1 ty2 then begin
          (* No dependency in the goal, but maybe there is a dependency in
             the pair itself. *)
          try
            let name', _, tBbody = destLambda !evd tB in
            if Vars.noccurn !evd 1 tBbody then
              (* No dependency whatsoever. *)
              let tsimpl_sigma = Globnames.ConstRef (Lazy.force EqRefs.simpl_sigma) in
              let tP = Termops.pop tBbody in
              let tB = Termops.pop ty2 in
              let args = [Some tA; Some tP; Some tB; Some tt; Some tu;
                          Some tp; Some tq; None] in
                tsimpl_sigma, args
            else raise Constr.DestKO
          with
          | Constr.DestKO ->
              (* Dependency in the pair, but not in the goal. *)
              let tsimpl_sigma = Globnames.ConstRef (Lazy.force EqRefs.simpl_sigma_dep) in
              let tP = tB in
              let tB = Termops.pop ty2 in
              let args = [Some tA; Some tP; Some tB; Some tt; Some tu;
                          Some tp; Some tq; None] in
              tsimpl_sigma, args
        end else
          (* We assume full dependency. We could add one more special case,
           * but we don't for now. *)
          let tsimpl_sigma = Globnames.ConstRef (Lazy.force EqRefs.simpl_sigma_dep_dep) in
          let tP = tB in
          let tB = EConstr.mkLambda (name, ty1, ty2) in
          let args = [Some tA; Some tP; Some tt; Some tu;
                      Some tp; Some tq; Some tB; None] in
            tsimpl_sigma, args
    | _, _ -> raise (CannotSimplify (str "If you see this, please report."))
  in build_app_infer env evd (ctx, ty) ctx f args, Covering.id_subst ctx
let remove_sigma = while_fun remove_one_sigma

let deletion ~(force:bool) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let tA, tx, _ = check_equality env !evd ctx ~equal_terms:true ty1 in
  let subst = Covering.id_subst ctx in
  if Vars.noccurn !evd 1 ty2 then
    (* The goal does not depend on the equality, we can just eliminate it. *)
    build_term env evd (ctx, ty) (ctx, Termops.pop ty2)
      (fun c -> EConstr.mkLambda (name, ty1, Vars.lift 1 c)),
    subst
  else
    let tB = EConstr.mkLambda (name, ty1, ty2) in
    try
      if not !Equations_common.simplify_withK_dec then raise Not_found else
      (* We will try to find an instance of K for the type [A]. *)
      let tsimpl_K_dec = Globnames.ConstRef (Lazy.force EqRefs.simpl_K_dec) in
      let eqdec_ty = EConstr.mkApp (Builder.eq_dec evd, [| tA |]) in
      let tdec =
        let env = push_rel_context ctx env in
          Equations_common.evd_comb1
            (Typeclasses.resolve_one_typeclass env) evd eqdec_ty
      in
      let args = [Some tA; Some tdec; Some tx; Some tB; None] in
        build_app_infer env evd (ctx, ty) ctx tsimpl_K_dec args, subst
    with Not_found ->
      if force || !Equations_common.simplify_withK then
        (* We can use K as an axiom. *)
        let tsimpl_K = Globnames.ConstRef (Lazy.force EqRefs.simpl_K) in
        let args = [Some tA; Some tx; Some tB; None] in
          build_app_infer env evd (ctx, ty) ctx tsimpl_K args, subst
      else
        let env = push_rel_context ctx env in
        raise (CannotSimplify (str
          "[deletion] Cannot simplify without K on type " ++
          Printer.pr_econstr_env env !evd tA))

let solution ~(dir:direction) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let name, ty1, ty2 = check_prod !evd ty in
  let tA, tx, tz = check_equality env !evd ctx ~var_left ~var_right ty1 in
  let trel, term =
    if var_left then tx, tz
    else tz, tx
  in
  let rel = EConstr.destRel !evd trel in
  let () =
    if Int.Set.mem rel (Covering.dependencies_of_term ~with_red:true env !evd ctx term rel) then
      raise (CannotSimplify (str  "[solution] The variable appears on both sides of the equality."))
  in
  (* let () = Feedback.msg_debug (str "solution on " ++ Printer.pr_econstr_env (push_rel_context ctx env) !evd ty) in *)
  let (ctx', _, _) as subst, rev_subst = Covering.new_strengthen env !evd ctx rel term in
  let trel' = Covering.mapping_constr !evd subst trel in
  let rel' = EConstr.destRel !evd trel' in
  let term' = Covering.mapping_constr !evd subst term in
  let tA' = Covering.mapping_constr !evd subst tA in
  let ty1' = Covering.mapping_constr !evd subst ty1 in
  (* We will have to generalize everything after [x'] in the new
   * context. *)
  let after', decl', before' = Covering.split_context (pred rel') ctx' in
  let name' = Context.Rel.Declaration.get_name decl' in
  (* let after, _, before = Covering.split_context rel ctx in*)
  
  (* Select the correct solution lemma. *)
  let nondep = Vars.noccurn !evd 1 ty2 in
  let tsolution = begin match var_left, nondep with
  | false, false -> Builder.solution_right_dep
  | false, true -> Builder.solution_right
  | true, false -> Builder.solution_left_dep
  | true, true -> Builder.solution_left end evd
  in
  let tB', body =
    let body = Covering.mapping_constr !evd subst ty in
    (* Right now, [body] has an equality at the head that we want
     * to move, in some sense. *)
    let _, _, body = EConstr.destProd !evd body in
    if nondep then
      let body = Termops.pop body in
      let body' = EConstr.it_mkProd_or_LetIn body after' in
        (* [body] is a term in the context [decl' :: before'],
         * whereas [tA'] lives in [ctx']. *)
        EConstr.mkLambda (name', Vars.lift (-rel') tA', body'), body
    else
      (* We make some room for the equality. *)
      let body = Vars.liftn 1 (succ rel') body in
      let body = Vars.subst1 (EConstr.mkRel rel') body in
      let after' = Equations_common.lift_rel_context 1 after' in
      let body' = EConstr.it_mkProd_or_LetIn body after' in
      let body' = EConstr.mkLambda (name, Vars.lift (1-rel') ty1', body') in
        EConstr.mkLambda (name', Vars.lift (-rel') tA', body'), body
  in
  (* [tB'] is a term in the context [before']. We want it in [ctx']. *)
  let tB' = Vars.lift rel' tB' in
  let targs' = Equations_common.extended_rel_vect 1 after' in
  (* [ctx''] is just [ctx'] where we replaced the substituted variable. *)
  let ctx'' = Equations_common.subst_in_ctx rel' term' ctx' in
  let after'', _ = CList.chop (pred rel') ctx'' in
  let ty'' =
    if nondep then
      Vars.substnl [Vars.lift (-rel') term'] (pred rel') body
    else
      let teq_refl = EConstr.mkApp (Builder.eq_refl evd, [| tA'; term' |]) in
        Vars.substnl [Vars.lift (-rel') teq_refl; Vars.lift (-rel') term'] (pred rel') body
  in
  let lsubst = Covering.single_subst env !evd rel' (Covering.pat_of_constr !evd term') ctx' in
  let subst = Covering.compose_subst env ~sigma:!evd lsubst subst in
  let f = fun c ->
      (* [c] is a term in the context [ctx'']. *)
      let c = EConstr.it_mkLambda_or_LetIn c after'' in
      (* [c] is a term in the context [before']. *)
      let c = Vars.lift rel' c in
      (* [c] is a term in the context [ctx']. *)
      let c =
        if nondep then
          EConstr.mkApp (tsolution, [| tA'; tB'; term'; c; trel' |])
        else
          EConstr.mkApp (tsolution, [| tA'; term'; tB'; c; trel' |])
      in
      (* We make some room for the application of the equality... *)
      let c = Vars.lift 1 c in
      let c = EConstr.mkApp (c, [| EConstr.mkRel 1 |]) in
      (* [targs'] are arguments in the context [eq_decl :: ctx']. *)
      let c = EConstr.mkApp (c, targs') in
      (* [ty1'] is the type of the equality in [ctx']. *)
      let c = EConstr.mkLambda (name, ty1', c) in
      (* And now we recover a term in the context [ctx]. *)
        Covering.mapping_constr !evd rev_subst c
  in build_term env evd (ctx, ty) (ctx'', ty'') f, subst

let pre_solution ~(dir:direction) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let var_left = match dir with Left -> true | Right -> false in
  let var_right = not var_left in
  let name, ty1, ty2 = check_prod !evd ty in
  let tA, tx, tz = check_equality env !evd ctx ~var_left ~var_right ty1 in
  let trel, term =
    if var_left then tx, tz
    else tz, tx
  in
  let rel = EConstr.destRel !evd trel in
  (** Check dependencies in both tA and term *)
  if not (Int.Set.mem rel (Covering.dependencies_of_term ~with_red:false env !evd ctx (mkApp (tA, [| term |])) rel)) then
    identity env evd (ctx, ty)
  else
    let tA = Reductionops.whd_all (push_rel_context ctx env) !evd tA in
    let term = Reductionops.whd_all (push_rel_context ctx env) !evd term in
    if Int.Set.mem rel (Covering.dependencies_of_term ~with_red:false env !evd ctx (mkApp (tA, [|term|])) rel) then
      raise (CannotSimplify (str  "[solution] cannot remove dependency in the variable "))
    else
      let f c = c in
      let eqf, _ = Equations_common.decompose_appvect !evd ty1 in
      let ty1 =
        if var_left then mkApp (eqf, [| tA; trel; term |])
        else mkApp (eqf, [| tA; term; trel |])
      in
      let ty' = mkProd (name, ty1, ty2) in
      build_term env evd (ctx, ty) (ctx, ty') f, Covering.id_subst ctx

let is_construct_sigma_2 sigma f =
  let term = match decompose_sigma sigma f with
    | Some (_, _, _, t) -> t
    | None -> f
  in
  let head, _ = EConstr.decompose_app sigma term in
  EConstr.isConstruct sigma head

(* Auxiliary steps for noConfusion. *)
let maybe_pack : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let tA, t1, t2 = check_equality env !evd ctx ty1 in
  if not (is_construct_sigma_2 !evd t1 && is_construct_sigma_2 !evd t2) then
    raise (CannotSimplify (str "This is not an equality between constructors."));
  let indty =
    try Inductiveops.find_rectype env !evd tA
    with Not_found ->
      raise (CannotSimplify (str "This is not an equality between constructors."));
  in
  let has_noconf () =
    let noconf_ty = EConstr.mkApp (Builder.noConfusion evd, [| tA |]) in
    let env = push_rel_context ctx env in
    try
      let _noconf = Equations_common.evd_comb1
          (Typeclasses.resolve_one_typeclass env) evd noconf_ty in
      true
    with Not_found -> false
  in
  let indfam, args = Inductiveops.dest_ind_type indty in
  if CList.is_empty args then
    identity env evd (ctx, ty)
  else if has_noconf () then
    identity env evd (ctx, ty)
  else begin
    (* We need to apply [simplify_ind_pack]. *)
    let ind, params = Equations_common.dest_ind_family indfam in
    let evd', tBfull, _, _, valsig, _, _, tA' = Sigma_types.build_sig_of_ind env !evd ind in
    evd := evd';
    let tA' = Vars.substl (List.rev params) tA' in
    (* We will try to find an instance of K for the type [A]. *)
    let eqdec_ty = EConstr.mkApp (Builder.eq_dec evd, [| tA' |]) in
    let tdec =
      let env = push_rel_context ctx env in
      try
        Equations_common.evd_comb1
          (Typeclasses.resolve_one_typeclass env) evd eqdec_ty
      with Not_found ->
        raise (CannotSimplify (str
          "[noConfusion] Cannot simplify without K on type " ++
          Printer.pr_econstr_env env !evd tA' ++
          str " or NoConfusion for family " ++ Printer.pr_inductive env (fst ind)))
    in
    let tx =
      let _, _, tx, _ = Option.get (decompose_sigma !evd valsig) in
        Vars.substl (CList.rev args) (Termops.pop tx)
    in
    let tsimplify_ind_pack = Globnames.ConstRef (Lazy.force EqRefs.simplify_ind_pack) in
    let tB = Reductionops.beta_applist !evd (tBfull, params) in
    (* FIXME Inserted this to simplify tB when it has the shape:
               {index & let H := index in foo H}
             Is this correct? *)
    let tB = let env = push_rel_context ctx env in
      Tacred.simpl env !evd tB in
    let tG = EConstr.mkLambda (name, ty1, ty2) in
    let args = [Some tA; Some tdec; Some tB; Some tx; Some t1; Some t2; Some tG; None] in
      build_app_infer env evd (ctx, ty) ctx tsimplify_ind_pack args, Covering.id_subst ctx
  end

let apply_noconf : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  let tA, t1, t2 = check_equality env !evd ctx ty1 in
  if not (is_construct_sigma_2 !evd t1 && is_construct_sigma_2 !evd t2) then
    raise (CannotSimplify (str "This is not an equality between constructors."));
  let noconf_ty = EConstr.mkApp (Builder.noConfusion evd, [| tA |]) in
  let tnoconf =
    let env = push_rel_context ctx env in
    try
      Equations_common.evd_comb1
        (Typeclasses.resolve_one_typeclass env) evd noconf_ty
    with Not_found ->
      raise (CannotSimplify (str
        "[noConfusion] Cannot find an instance of NoConfusion for type " ++
        Printer.pr_econstr_env env !evd tA))
  in
  let tapply_noconf = Globnames.ConstRef (Lazy.force EqRefs.apply_noConfusion) in
  let tB = EConstr.mkLambda (name, ty1, ty2) in
  let args = [Some tA; Some tnoconf; Some t1; Some t2; Some tB; None] in
    build_app_infer env evd (ctx, ty) ctx tapply_noconf args, Covering.id_subst ctx

let simplify_ind_pack_inv : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  (* FIXME Can't ignore _all_ errors? *)
  try
    let reduce c =
      let env = push_rel_context ctx env in
        Tacred.hnf_constr env !evd c
    in
    let try_decompose ty =
      let f, args = Equations_common.decompose_appvect !evd ty in
      if not (check_constant !evd (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f) ||
         not (Int.equal 8 (Array.length args)) then
        raise (CannotSimplify (str
          "Expected a full application of [opaque_ind_pack_eq_inv]. Maybe\
           you did not solve completely a NoConfusion step?"));
      f, args
    in
    let (f, args), ty =
      try try_decompose ty, ty with CannotSimplify _ ->
        let ty = reduce ty in
        try_decompose ty, ty
    in
    let tA = args.(0) in
    let teqdec = args.(1) in
    let tB = args.(2) in
    let tx = args.(3) in
    let tp = args.(4) in
    let tG = args.(6) in
    let teq = args.(7) in
    (* Check that [teq] is [eq_refl]. *)
    let tsigma = EConstr.mkApp (Builder.sigma evd, [| tA; tB |]) in
    let tsigmaI = EConstr.mkApp (Builder.sigmaI evd, [| tA; tB; tx; tp |]) in
    let teq_refl = EConstr.mkApp (Builder.eq_refl evd, [| tsigma; tsigmaI |]) in
    if not (is_conv env !evd ctx teq teq_refl) then
      (* FIXME Horrible error message... *)
      raise (CannotSimplify (str
        "[opaque_ind_pack_eq_inv] should be applied to [eq_refl]."));
    let tsimplify_ind_pack_inv = Globnames.ConstRef (Lazy.force EqRefs.simplify_ind_pack_inv) in
    let args = [Some tA; Some teqdec; Some tB; Some tx; Some tp; Some tG; None] in
      build_app_infer env evd (ctx, ty) ctx tsimplify_ind_pack_inv args,
      Covering.id_subst ctx
  with CannotSimplify _ -> identity env evd (ctx, ty)

let noConfusion = compose_fun apply_noconf maybe_pack

let noCycle : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  failwith "[noCycle] is not implemented!"

let elim_true : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  if not (check_inductive !evd (Lazy.force EqRefs.one) ty1) then
    raise (CannotSimplify (str
      "[elim_true] The first hypothesis is not the unit type."));
  let subst = Covering.id_subst ctx in
  (* Check if the goal is dependent or not. *)
  if Vars.noccurn !evd 1 ty2 then
    (* Not dependent, we can just eliminate True. *)
    build_term env evd (ctx, ty) (ctx, Termops.pop ty2)
      (fun c -> EConstr.mkLambda (name, ty1, Vars.lift 1 c)), subst
  else
    (* Apply the dependent induction principle for True. *)
    let tB = EConstr.mkLambda (name, ty1, ty2) in
    let tone_ind = Globnames.ConstRef (Lazy.force EqRefs.one_ind_dep) in
    let args = [Some tB; None] in
      build_app_infer env evd (ctx, ty) ctx tone_ind args, subst

let elim_false : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let name, ty1, ty2 = check_prod !evd ty in
  if not (check_inductive !evd (Lazy.force EqRefs.zero) ty1) then
    raise (CannotSimplify (str
      "[elim_true] The first hypothesis is not the empty type."));
  let subst = Covering.id_subst ctx in
  let tB, tzero_ind =
  (* Check if the goal is dependent or not. *)
    if Vars.noccurn !evd 1 ty2 then
      let tB = Termops.pop ty2 in
      let tzero_ind = Builder.zero_ind evd in
        tB, tzero_ind
    else
      let tB = EConstr.mkLambda (name, ty1, ty2) in
      let tzero_ind = Builder.zero_ind_dep evd in
        tB, tzero_ind
  in
  let c = EConstr.mkApp (tzero_ind, [| tB |]) in
  (* We need to type the term in order to solve eventual universes
   * constraints. *)
  let _ = let env = push_rel_context ctx env in
          Equations_common.evd_comb1 (Typing.type_of env) evd c in
    (None, c), subst


(* Inference mechanism. *)

let infer_step ?(loc:Loc.t option) ~(isSol:bool)
  (env : Environ.env) (evd : Evd.evar_map ref)
  ((ctx, ty) : goal) : simplification_step =
  (* The goal does not have to be a product, but if it's not, it has to be
   * an application of [opaque_ind_pack_eq_inv]. *)
  let f, _ = Equations_common.decompose_appvect !evd ty in
  if check_constant !evd (Lazy.force EqRefs.opaque_ind_pack_eq_inv) f then
    NoConfusionOut
  else begin
    let name, ty1, ty2 = check_prod !evd ty in
    (* First things first, maybe the head of the goal is False or True. *)
    if check_inductive !evd (Lazy.force EqRefs.zero) ty1 then ElimFalse
    else if check_inductive !evd (Lazy.force EqRefs.one) ty1 then ElimTrue
    else
    (* We need to destruct the equality at the head
       to analyze it. *)
    let tA, tu, tv = check_equality env !evd ctx ty1 in
    (* FIXME What is the correct way to do it? *)
    let choose u v = Left (* if u < v then Left else Right *) in
    (* If the user wants a solution, we need to respect his wishes. *)
    if isSol then
      if EConstr.isRel !evd tu && EConstr.isRel !evd tv then
        Solution (choose (EConstr.destRel !evd tu) (EConstr.destRel !evd tv))
      else if EConstr.isRel !evd tu then Solution Left
      else if EConstr.isRel !evd tv then Solution Right
      else raise (CannotSimplify (str "Neither side of the equality is a variable."))
    else begin
      let check_occur trel term =
        let rel = EConstr.destRel !evd trel in
          not (Int.Set.mem rel (Covering.dependencies_of_term ~with_red:true env !evd ctx term rel))
      in
      if EConstr.isRel !evd tu && EConstr.isRel !evd tv && check_occur tu tv then
        Solution (choose (EConstr.destRel !evd tu) (EConstr.destRel !evd tv))
      else if EConstr.isRel !evd tu && check_occur tu tv then Solution Left
      else if EConstr.isRel !evd tv && check_occur tv tu then Solution Right
      else
      let check_ind t =
        let f, _ = EConstr.decompose_app !evd t in
        try ignore (Inductive.find_rectype env (to_constr !evd f)); true
        with Not_found -> false
      in
      let check_construct t =
        let f, _ = EConstr.decompose_app !evd t in
        let env = push_rel_context ctx env in
        let f = Tacred.hnf_constr env !evd f in
          EConstr.isConstruct !evd f
      in
      (* FIXME What is the correct order here? Should we first check if we
       * have K directly? *)
      if is_conv env !evd ctx tu tv then
        Deletion false (* Never force K. *)
      else if check_ind tA && check_construct tu && check_construct tv then
        NoConfusion [loc, Infer_many]
      else
      (* Check if [u] occurs in [t] under only constructors. *)
      (* For now we don't care about the type of these constructors. *)
      (* Note that we also don't need to care about binders, since we can
         only go through constructors and nothing else. *)
      let check_occur t u =
        let eq t = eq_constr !evd t u in
        let rec aux t =
          if eq t then raise Termops.Occur;
          let f, args = EConstr.decompose_app !evd t in
          if EConstr.isConstruct !evd f then
            CList.iter aux args
        in try aux t; false
        with Termops.Occur -> true
      in
      if check_occur tu tv || check_occur tv tu then NoCycle
      else
        raise (CannotSimplify (str "Could not infer a simplification step."))
    end
  end

let or_fun (f : simplification_fun) (g : simplification_fun) : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) (gl : goal) ->
  let evd0 = !evd in
  try f env evd gl
  with CannotSimplify _ ->
    evd := evd0; g env evd gl

let _expand_many rule env evd ((ctx, ty) : goal) : simplification_rules =
  (* FIXME: maybe it's too brutal/expensive? *)
  let ty = Reductionops.whd_all env !evd ty in
  let _, ty, _ = check_prod !evd ty in
  try
    let ty = Reductionops.whd_all env !evd ty in
    let ty, _, _ = check_equality env !evd ctx ty in
    let rec aux ty acc =
      let ty = Reductionops.whd_betaiotazeta !evd ty in
      let f, args = Equations_common.decompose_appvect !evd ty in
      if check_inductive !evd (Lazy.force SigmaRefs.sigma) f then
        let next_ty = Reductionops.beta_applist !evd (args.(1), [EConstr.mkRel 1]) in
        aux next_ty (rule :: acc)
      else acc
    in aux ty [rule]
  with CannotSimplify _ -> [rule]

exception Blocked

let check_block : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty) : goal) ->
  let _na, _b, _ty, _b' = check_letin !evd ty in
  raise Blocked

let check_block_notprod : simplification_fun =
  fun (env : Environ.env) (evd : Evd.evar_map ref) ((ctx, ty as gl) : goal) ->
    try let _ = destLetIn !evd ty in
      identity env evd gl
    with Constr.DestKO ->
    try
      let env = push_rel_context ctx env in
      let ty = Reductionops.whd_all env !evd ty in
      let _na, _ty, _ty' = EConstr.destProd !evd ty in
      raise (CannotSimplify (str"a product"))
    with Constr.DestKO -> identity env evd gl

let rec apply_noConfusions =
  fun env evd goal ->
    or_fun noConfusion
      (compose_fun apply_noConfusions remove_one_sigma) env evd goal

(* Execution machinery. *)

let rec execute_step : simplification_step -> simplification_fun = function
  | Deletion force -> deletion ~force
  | Solution dir -> compose_fun (solution ~dir:dir) (pre_solution ~dir:dir)
  (* FIXME Not enough retries? *)
  | NoConfusion rules ->
      let noconf_out = (*with_retry*) simplify_ind_pack_inv in
        compose_fun noconf_out (compose_fun (simplify rules) noConfusion)
  | NoConfusionOut -> simplify_ind_pack_inv
  | NoCycle -> noCycle
  | ElimTrue -> elim_true
  | ElimFalse -> elim_false

and simplify_one ((loc, rule) : Loc.t option * simplification_rule) :
  simplification_fun =
  let handle_error f =
    fun env evd gl ->
      try f env evd gl
      with CannotSimplify err ->
        Equations_common.user_err_loc (loc, "Equations.Simplify", err)
  in
  let wrap get_step =
    let f = fun env evd gl ->
      let step = get_step env evd gl in
        execute_step step env evd gl
    in
    let f = compose_fun f remove_sigma in
    with_retry f
  in
  let wrap_handle get_step =
    let f = wrap get_step in
    handle_error f
  in
  match rule with
  | Infer_many ->
     let rec aux env evd gl =
       let first =
         or_fun check_block
           (or_fun (with_retry apply_noConfusions)
              (wrap (infer_step ?loc ~isSol:false)))
       in
       try compose_fun (or_fun check_block_notprod aux)
             first env evd gl
       with Blocked -> identity env evd gl
     in handle_error aux
  | Step step -> wrap_handle (fun _ _ _ -> step)
  | Infer_one -> handle_error (or_fun (with_retry apply_noConfusions)
                                 (wrap (infer_step ?loc ~isSol:false)))
  | Infer_direction -> wrap_handle (infer_step ?loc ~isSol:true)

and simplify (rules : simplification_rules) : simplification_fun =
  let funs = List.rev_map simplify_one rules in
    match funs with
    | [] -> identity
    | hd :: tl -> List.fold_left compose_fun hd tl

let simplify_tac (rules : simplification_rules) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let env = Environ.reset_context (Proofview.Goal.env gl) in
    let hyps = Proofview.Goal.hyps gl in
    (* Keep aside the section variables. *)
    let loc_hyps, sec_hyps = CList.split_when
      (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        Termops.is_section_variable id) hyps in
    let env = push_named_context sec_hyps env in
    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Equations_common.rel_of_named_context loc_hyps in
    let _, rev_subst, _ =
      let err () = assert false in
      Equations_common.named_of_rel_context ~keeplets:true err ctx in
    let concl = Proofview.Goal.concl gl in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars subst concl in
    (* [ty'] is the expected type of the hole in the term, under the
     * context [ctx']. *)
    Refine.refine ~typecheck:true (fun evars ->
      let evd = ref evars in
      let (_, c), _ = simplify rules env evd (ctx, ty) in
      let c = Vars.substl (List.rev rev_subst) c in
         (!evd, c)))


(* Printing functions. *)

let pr_simplification_step : simplification_step -> Pp.t = function
  | Deletion false -> str "-"
  | Deletion true -> str "-!"
  | Solution (Left) -> str "->"
  | Solution (Right) -> str "<-"
  | NoConfusion rules -> str "$"
  | NoConfusionOut -> str "NoConfusionOut"
  | NoCycle -> str "NoCycle"
  | ElimTrue -> str "ElimTrue"
  | ElimFalse -> str "ElimFalse"

let pr_simplification_rule ((_, rule) : Loc.t option * simplification_rule) :
  Pp.t = match rule with
  | Infer_one -> str "?"
  | Infer_direction -> str "<->"
  | Infer_many -> str "*"
  | Step step -> pr_simplification_step step

let pr_simplification_rules : simplification_rules -> Pp.t =
  prlist_with_sep spc pr_simplification_rule
