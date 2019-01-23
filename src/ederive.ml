(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr

type derive_fn_ty = polymorphic:bool -> Names.GlobRef.t -> unit

type derive_record =
  { derive_name : string;
    derive_fn : polymorphic:bool -> Names.GlobRef.t -> unit }

let make_derive fn ~polymorphic s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evarutil.new_global sigma s in
  fn env sigma ~polymorphic c

let make_derive_ind fn ~polymorphic s =
  let fn env sigma ~polymorphic c =
    match EConstr.kind sigma c with
    | Ind (i,u) -> fn env sigma ~polymorphic (i,u)
    | _ -> CErrors.user_err (Pp.str"Expected an inductive type")
  in make_derive fn ~polymorphic s
                 
let table = ref (CString.Map.empty : derive_fn_ty CString.Map.t)
    
let register_derive d =
  table := CString.Map.add d.derive_name d.derive_fn !table

let get_derive d =
  try CString.Map.find d !table
  with Not_found -> CErrors.user_err Pp.(str"No derive declared for " ++ str d)
                                 
let derive_one polymorphic d grs =
  let fn = get_derive d in
  List.iter (fun x -> fn ~polymorphic x) grs

let derive ~poly ds grs =
  let grs = List.map (fun (loc, gr) -> Dumpglob.add_glob ?loc gr; gr) grs in
  List.iter (fun d -> derive_one poly d grs) ds
