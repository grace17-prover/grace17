(* Command-line G17M proof-tape checker.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support

let () =
  try
    let certificate = ref None and environment = ref None in
    let usage = "usage: g17check CERTIFICATE --environment ENVIRONMENT [--fuel STEPS]" in
    let rec args = function
      | [] -> ()
      | "--environment" :: v :: xs ->
          environment := Some v ;
          args xs
      | "--fuel" :: v :: xs ->
          (match int_of_string_opt v with
          | Some n when n > 0 -> Compute.default_fuel := n
          | _ -> fail "--fuel must be a positive integer") ;
          args xs
      | v :: xs when !certificate = None -> certificate := Some v ; args xs
      | _ -> fail usage
    in
    args (List.tl (Array.to_list Sys.argv)) ;
    let certificate, environment =
      match (!certificate, !environment) with
      | Some p, Some e -> (p, e)
      | _ -> fail usage
    in
    let instructions, theorems =
      Machine.verify (Machine.decode certificate) (parse (read_file environment))
    in
    Printf.printf "ACCEPT: %d instructions, %d theorem boundaries\n" instructions
      theorems
  with
  | Reject msg ->
      Printf.eprintf "REJECT: %s\n" msg ;
      exit 1
  | Sys_error msg ->
      Printf.eprintf "ERROR: %s\n" msg ;
      exit 1
  | Stack_overflow | Out_of_memory ->
      prerr_endline "REJECT: resource limit" ;
      exit 1
  | exn ->
      Printf.eprintf "REJECT: %s\n" (Printexc.to_string exn) ;
      exit 1
