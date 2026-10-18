(* Command-line G17C compiled-module checker.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support

let () =
  try
    let certificate = ref None
    and foundation = ref None
    and dependencies = ref []
    and json = ref false in
    let rec args = function
      | [] -> ()
      | "--foundation" :: v :: xs ->
          foundation := Some v ;
          args xs
      | "--dependency" :: v :: xs ->
          dependencies := !dependencies @ [v] ;
          args xs
      | "--json" :: xs ->
          json := true ;
          args xs
      | "--fuel" :: v :: xs ->
          (match int_of_string_opt v with
          | Some n when n > 0 -> Compute.default_fuel := n
          | _ -> fail "--fuel must be a positive integer") ;
          args xs
      | v :: xs when !certificate = None ->
          certificate := Some v ;
          args xs
      | _ ->
          fail
            "usage: g17c_check CERTIFICATE --foundation ZFG [--dependency FILE] \
             [--json] [--fuel STEPS]"
    in
    args (List.tl (Array.to_list Sys.argv)) ;
    let cert =
      match !certificate with Some x -> x | None -> fail "missing certificate"
    in
    let foundation =
      match !foundation with Some x -> x | None -> fail "missing foundation"
    in
    let e, root = Compiled.check cert foundation !dependencies in
    let result =
      Obj
        [ ("ok", Bool true)
        ; ("checker", Str "grace17-ocaml-g17c")
        ; ("version", Num 3)
        ; ("module", get root "module")
        ; ("events", Num (List.length (arr (get root "events"))))
        ; ("theorems", Num (Hashtbl.length e.Environment.theorems))
        ; ("environment", Str e.digest) ]
    in
    if !json then print_endline (canonical result)
    else
      Printf.printf "ACCEPT: %s (%d events), environment %s\n"
        (str (get root "module"))
        (List.length (arr (get root "events")))
        e.digest
  with
  | Reject msg | Sys_error msg ->
      Printf.eprintf "REJECT: %s\n" msg ;
      exit 1
  | Stack_overflow | Out_of_memory ->
      prerr_endline "REJECT: resource limit" ;
      exit 1
  | exn ->
      Printf.eprintf "REJECT: %s\n" (Printexc.to_string exn) ;
      exit 1
