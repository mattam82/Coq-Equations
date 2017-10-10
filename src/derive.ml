(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term

type derive_fn_ty = polymorphic:bool -> Globnames.global_reference -> unit

type derive_record =
  { derive_name : string;
    derive_fn : polymorphic:bool -> Globnames.global_reference -> unit }

let make_derive fn ~polymorphic s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let Sigma.Sigma (c, sigma, _) = Evarutil.new_global (Sigma.Unsafe.of_evar_map sigma) s in
  fn env (Sigma.to_evar_map sigma) ~polymorphic c

let make_derive_ind fn ~polymorphic s =
  let fn env sigma ~polymorphic c =
    match kind_of_term c with
    | Ind i -> fn env sigma ~polymorphic i
    | _ -> CErrors.error "Expected an inductive type"
  in make_derive fn ~polymorphic s
                 
let table = ref (CString.Map.empty : derive_fn_ty CString.Map.t)
    
let register_derive d =
  table := CString.Map.add d.derive_name d.derive_fn !table

let get_derive d =
  try CString.Map.find d !table
  with Not_found -> CErrors.error ("No derive declared for " ^ d)
                                 
let derive_one polymorphic d grs =
  let fn = get_derive d in
  List.iter (fun x -> fn ~polymorphic x) grs

let derive ds grs =
  let poly = Flags.use_polymorphic_flag () in
  let grs = List.map (fun (loc, gr) -> Dumpglob.add_glob loc gr; gr) grs in
  List.iter (fun d -> derive_one poly d grs) ds
