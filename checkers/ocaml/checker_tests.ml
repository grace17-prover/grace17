(* Unit tests for the OCaml checkers; a separate executable that neither CLI links.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support

let replace key value j = Obj ((key, value) :: List.remove_assoc key (obj j))

let rejects f =
  let rejected = try f () ; false with Reject _ -> true in
  require rejected "invalid unit declaration accepted"

let unit_admission path =
  let fixture = parse (read_file path) in
  let base () =
    let e = Foundation.construct "ZFG" in
    List.iter
      (function
        | Arr [Str n; f] -> Environment.add_axiom e n f | _ -> fail "unit axiom shape"
        )
      (arr (get fixture "axioms")) ;
    e
  in
  let events = arr (get fixture "events") in
  let e = base () in
  List.iter (Admissions.replay e) events ;
  Environment.refresh e ;
  require
    (e.digest = str (get fixture "environment"))
    "well-founded admission differs from reference" ;
  let event = List.hd events in
  let payload = get event "payload" in
  let options = get payload "options" in
  let bad_proof = replace "wellFounded" (get options "measureInDomain") options in
  let bad_variable = replace "measure" (Named.v "undeclared") options in
  let equations = arr (get options "equations") in
  let last = List.nth equations 1 in
  let recursive = replace "body" (Named.app "wfConstant" [Named.v "n"]) last in
  let missing_decrease =
    replace "equations" (Arr [List.hd equations; recursive]) options
  in
  let wrong_decrease =
    replace "decreases" (Arr [get options "wellFounded"]) missing_decrease
  in
  List.iter
    (fun options ->
      let event = replace "payload" (replace "options" options payload) event in
      rejects (fun () -> Admissions.replay (base ()) event) )
    [bad_proof; bad_variable; missing_decrease; wrong_decrease] ;
  print_endline
    "OCaml declaration unit: exact well-founded environment and 4 invalid obligations \
     checked"

let arithmetic path =
  (* Numerals participate in structural formula equality and memo-table keys. *)
  let large = Z.shift_left Z.one 256 in
  let reconstructed = Z.of_string (Z.to_string large) in
  let term = Logic.N large and same = Logic.N reconstructed in
  require (term = same) "large numeral structural equality" ;
  let memo = Hashtbl.create 1 in
  Hashtbl.add memo term true ;
  require (Hashtbl.find_opt memo same = Some true) "large numeral hashing" ;
  require
    ( Logic.app "succ" [Logic.N (Z.of_int max_int)]
    = Logic.N (Z.succ (Z.of_int max_int)) )
    "successor across host integer boundary" ;
  require (Compute.bounded_int (Z.of_int 17) 17 = 17) "exact fuel bound" ;
  rejects (fun () -> ignore (Compute.bounded_int large 1000000)) ;
  rejects (fun () -> ignore (Compute.bounded_int Z.minus_one 1000000)) ;
  rejects (fun () -> ignore (Compute.multiply (Z.shift_left Z.one 3321928) Z.one)) ;
  List.iter
    (fun value ->
      rejects (fun () ->
          ignore (Logic.term_json [] (Obj [("tag", Str "nat"); ("value", Str value)]))
      ) )
    ["-1"; "+1"; "01"; "0x10"; ""] ;
  let cases = arr (parse (read_file path)) in
  List.iter
    (fun c ->
      let a = Z.of_string (str (get c "a")) and b = Z.of_string (str (get c "b")) in
      require
        (Z.equal (Z.add a b) (Z.of_string (str (get c "add"))))
        "addition mismatch" ;
      require
        (Z.equal (Compute.multiply a b) (Z.of_string (str (get c "mul"))))
        "multiplication mismatch" ;
      require
        (Z.equal (Compute.truncated_sub a b) (Z.of_string (str (get c "sub"))))
        "truncated subtraction mismatch" )
    cases ;
  Printf.printf "OCaml arithmetic unit: %d independent expected-value cases checked\n"
    (List.length cases)

let () =
  try
    match Array.to_list Sys.argv with
    | [_; "admission"; path] -> unit_admission path
    | [_; "arithmetic"; path] -> arithmetic path
    | _ -> fail "checker_tests admission|arithmetic FILE"
  with Reject msg -> prerr_endline msg ; exit 1
