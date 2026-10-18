(* Known-answer tests for the support layer.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support

let () =
  List.iter
    (fun (s, wanted) -> assert (Sha256.digest s = wanted))
    [ ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    ; ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    ; ( String.make 1000000 'a'
      , "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" ) ] ;
  assert (
    canonical (parse "{\"z\":1,\"a\": [true, null, \"\\ud83d\\ude00\"]}")
    = "{\"a\":[true,null,\"😀\"],\"z\":1}" ) ;
  assert (
    canonical (Obj [("\xee\x80\x80", Num 1); ("😀", Num 2)])
    = "{\"😀\":2,\"\xee\x80\x80\":1}" ) ;
  List.iter
    (fun s ->
      let rejected =
        try
          ignore (parse s) ;
          false
        with Reject _ -> true
      in
      assert rejected )
    ["{\"x\":0,\"x\":1}"; "[1,]"; "01"; "\"\\ud800\""; "\"\xc0\x80\""; "true false"] ;
  print_endline
    "OCaml support: SHA-256 known answers, Unicode canonicalization, malformed JSON \
     passed"
