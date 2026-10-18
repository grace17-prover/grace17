(* G17C event and dependency replay.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

(* G17C v3 reconstructs the logical environment. No serialized environment is
   accepted as authority, and a theorem batch is installed only after replay. *)
open Support
module E = Environment

let digest s =
  String.length s = 64
  && String.for_all (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) s

let validate document =
  require
    ( get document "format" = Str "grace17.compiled-module"
    && get document "version" = Num 3 )
    "unsupported G17C version" ;
  let d = str (get document "digest") in
  require (digest d) "bad module digest" ;
  let body = Obj (List.filter (fun (k, _) -> k <> "digest") (obj document)) in
  require (Sha256.digest (canonical body) = d) "module digest mismatch" ;
  require (str (get document "module") <> "") "empty module name" ;
  ignore (arr (get document "events")) ;
  let source = str (get document "source") in
  require (source = "" || digest source) "bad source digest" ;
  List.iter
    (fun k -> require (digest (str (get document k))) ("bad " ^ k))
    ["baseEnvironment"; "resultEnvironment"] ;
  let dependencies = arr (get document "dependencies") in
  Logic.unique (List.map (fun d -> str (get d "module")) dependencies) ;
  List.iter
    (fun d ->
      require
        (str (get d "module") <> "" && digest (str (get d "digest")))
        "bad dependency" )
    dependencies ;
  document

let replay e document =
  let foundation = get document "foundation" in
  require
    ( get foundation "profile" = get e.E.capabilities "setTheory"
    && get foundation "environment" = Str e.foundation )
    "foundation mismatch" ;
  List.iter
    (fun d ->
      let n = str (get d "module") in
      require
        (Hashtbl.find_opt e.receipts n = Some (str (get d "digest")))
        ("missing dependency " ^ n) )
    (arr (get document "dependencies")) ;
  require
    (e.digest = str (get document "baseEnvironment"))
    "exact dependency prefix mismatch" ;
  List.iteri
    (fun index event ->
      try
        match str (get event "kind") with
        | "admission" -> Admissions.replay e (get event "event")
        | "theoremBatch" ->
            let statements = arr (get event "statements") in
            require (statements <> []) "empty theorem batch" ;
            let expected =
              List.map
                (fun s ->
                  let n = str (get s "name") and f = get s "statement" in
                  require
                    ( n <> ""
                    && not (Hashtbl.mem e.axioms n || Hashtbl.mem e.theorems n) )
                    "duplicate theorem" ;
                  E.closed e f ;
                  (n, f) )
                statements
            in
            Logic.unique (List.map fst expected) ;
            let program = Machine.from_json (get event "machine") in
            require
              ( List.sort compare (List.map fst expected)
              = List.sort compare
                  (List.map
                     (fun (n, _) -> Logic.at program.symbols n)
                     program.boundaries) )
              "theorem boundary set mismatch" ;
            ignore (Machine.verify_current ~statements:expected program (E.snapshot e)) ;
            List.iter (fun (n, f) -> Hashtbl.add e.theorems n f) expected
        | _ -> fail "unknown G17C event"
      with Reject msg -> fail (Printf.sprintf "event %d: %s" index msg) )
    (arr (get document "events")) ;
  E.refresh e ;
  require
    (e.digest = str (get document "resultEnvironment"))
    ("result environment mismatch: obtained " ^ e.digest) ;
  Hashtbl.replace e.receipts
    (str (get document "module"))
    (str (get document "digest"))

let check certificate foundation dependencies =
  let e = Foundation.load foundation in
  let root = validate (parse (read_file certificate)) in
  let supplied = List.map (fun p -> validate (parse (read_file p))) dependencies in
  List.iter
    (fun d ->
      let artifact =
        List.find_opt
          (fun a -> get a "digest" = get d "digest" && get a "module" = get d "module")
          supplied
      in
      match artifact with
      | None -> fail ("missing artifact " ^ str (get d "module"))
      | Some a -> replay e a )
    (arr (get root "dependencies")) ;
  replay e root ;
  (e, root)
