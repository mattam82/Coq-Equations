(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term

type derive_record =
  { derive_name : string;
    derive_fn : Globnames.global_reference -> unit }

let make_derive fn s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let Sigma.Sigma (c, sigma, _) = Evarutil.new_global (Sigma.Unsafe.of_evar_map sigma) s in
  fn env (Sigma.to_evar_map sigma) c

let make_derive_ind fn s =
  let fn env sigma c =
    match kind_of_term c with
    | Ind i -> fn env sigma i
    | _ -> CErrors.error "Expected an inductive type"
  in make_derive fn s
                 
let table = ref CString.Map.empty
    
let register_derive d =
  table := CString.Map.add d.derive_name d.derive_fn !table

let get_derive d =
  try CString.Map.find d !table
  with Not_found -> CErrors.error ("No derive declared for " ^ d)
                                 
let derive_one d grs =
  let fn = get_derive d in
  List.iter fn grs

let derive ds grs =
  List.iter (fun d -> derive_one d grs) ds
