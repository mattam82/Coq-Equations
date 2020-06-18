(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr

type derive_fn_ty = poly:bool -> Names.GlobRef.t -> unit

type derive_record =
  { derive_name : string;
    derive_fn : poly:bool -> Names.GlobRef.t -> unit }

let make_derive fn ~poly s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global ~rigid:Evd.univ_rigid env sigma s in
  fn env sigma ~poly c

let make_derive_ind fn ~poly s =
  let fn env sigma ~poly c =
    match EConstr.kind sigma c with
    | Ind (i,u) -> fn env sigma ~poly (i,u)
    | _ -> CErrors.user_err (Pp.str"Expected an inductive type")
  in make_derive fn ~poly s
                 
let table = ref (CString.Map.empty : derive_fn_ty CString.Map.t)
    
let register_derive d =
  table := CString.Map.add d.derive_name d.derive_fn !table

let get_derive d =
  try CString.Map.find d !table
  with Not_found -> CErrors.user_err Pp.(str"No derive declared for " ++ str d)

module StringOrd = struct type t = string let compare = String.compare end
module StringSet = Set.Make(StringOrd)

(** We keep a table of which derives have been performed yet for a given global reference. *)
type derive_instance = (string * Names.GlobRef.t)

type derive_instance_map = StringSet.t Names.GlobRef.Map.t

let derived_instances : derive_instance_map ref = Summary.ref Names.GlobRef.Map.empty ~name:"derived-instances"

let cache_instance (_, (derive, gr)) = 
  let grderives = 
    match Names.GlobRef.Map.find_opt gr !derived_instances with
    | Some s -> s
    | None -> StringSet.empty
  in
  derived_instances := Names.GlobRef.Map.add gr (StringSet.add derive grderives) !derived_instances

let subst_instance (subst, (derive, gr)) =
  (derive, fst (Globnames.subst_global subst gr))

let discharge_instance (na, (derive, gr)) =
  if Globnames.isVarRef gr then None
  else Some (derive, gr)

let derive_instance_input : derive_instance -> Libobject.obj =
  let decl = 
    Libobject.superglobal_object "derive instances state"
      ~cache:cache_instance
      ~discharge:discharge_instance
      ~subst:(Some subst_instance)
  in 
  Libobject.declare_object decl

let register_instance decl =
  Lib.add_anonymous_leaf (derive_instance_input decl)

let check_derive s gr =
  try
    let grds = Names.GlobRef.Map.find gr !derived_instances in
    StringSet.mem s grds
  with Not_found -> false
  
let derive_one poly d grs =
  let fn = get_derive d in
  List.iter (fun x -> fn ~poly x; register_instance (d, x)) grs

let derive ~poly ds grs =
  let grs = List.map (fun (loc, gr) -> Dumpglob.add_glob ?loc gr; gr) grs in
  List.iter (fun d -> derive_one poly d grs) ds
