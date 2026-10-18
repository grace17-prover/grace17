(* Signatures, closedness, and deterministic environment state.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Named

type table = (string, json) Hashtbl.t

type t =
  { capabilities: json
  ; functions: table
  ; predicates: table
  ; axioms: table
  ; theorems: table
  ; definitions: table
  ; datatypes: table
  ; recursive: table
  ; bodies: table
  ; receipts: (string, string) Hashtbl.t
  ; mutable digest: string
  ; mutable foundation: string }

let table () = Hashtbl.create 128

let create profile =
  require (List.mem profile ["ZF"; "ZFC"; "ZFG"]) "unknown foundation profile" ;
  { capabilities=
      Obj
        [ ("separation", Bool true)
        ; ("replacement", Bool true)
        ; ("inductiveDefinitions", Bool true)
        ; ("setTheory", Str profile) ]
  ; functions= table ()
  ; predicates= table ()
  ; axioms= table ()
  ; theorems= table ()
  ; definitions= table ()
  ; datatypes= table ()
  ; recursive= table ()
  ; bodies= table ()
  ; receipts= Hashtbl.create 8
  ; digest= ""
  ; foundation= "" }

let find table name =
  match Hashtbl.find_opt table name with
  | Some x -> x
  | None -> fail ("unknown logical name " ^ name)

let entries table =
  Hashtbl.fold (fun k v xs -> (k, v) :: xs) table []
  |> List.sort (fun (a, _) (b, _) -> compare (utf16 a) (utf16 b))

let associations pairs = Arr (List.map (fun (k, v) -> Arr [Str k; v]) pairs)

let snapshot e =
  Obj
    [ ("capabilities", e.capabilities)
    ; ("functions", associations (entries e.functions))
    ; ("predicates", associations (entries e.predicates))
    ; ("axioms", associations (entries e.axioms))
    ; ("theorems", associations (entries e.theorems))
    ; ("definitions", associations (entries e.definitions))
    ; ("datatypes", associations (entries e.datatypes))
    ; ("recursiveFunctions", associations (entries e.recursive))
    ; ("functionBodies", associations (entries e.bodies)) ]

let refresh e = e.digest <- Sha256.digest (canonical (snapshot e))

let parameters ps =
  Logic.unique ps ;
  List.iter (fun p -> require (p <> "") "empty parameter") ps

let fresh_name e n =
  require
    ( n <> ""
    && not
         ( Hashtbl.mem e.functions n || Hashtbl.mem e.predicates n
         || Hashtbl.mem e.definitions n ) )
    ("duplicate logical symbol " ^ n)

let declare e table n arity =
  fresh_name e n ;
  require (arity >= 0 && arity <= 0xffffffff) "bad arity" ;
  Hashtbl.add table n (Num arity)

let rec check_term e t =
  match tag t with
  | "var" -> require (str (get t "name") <> "") "empty variable"
  | "nat" -> require (Logic.natural (str (get t "value"))) "bad natural"
  | "app" ->
      let args = arr (get t "args") in
      require
        (find e.functions (str (get t "fn")) = Num (List.length args))
        "function arity" ;
      List.iter (check_term e) args
  | _ -> fail "bad term"

let rec check_formula e f =
  match tag f with
  | "bottom" -> ()
  | "eq" ->
      check_term e (get f "left") ;
      check_term e (get f "right")
  | "pred" ->
      let args = arr (get f "args") in
      require
        (find e.predicates (str (get f "pred")) = Num (List.length args))
        "predicate arity" ;
      List.iter (check_term e) args
  | "imp" | "and" | "or" | "iff" ->
      check_formula e (get f "left") ;
      check_formula e (get f "right")
  | "forall" | "exists" ->
      require (str (get f "variable") <> "") "empty binder" ;
      check_formula e (get f "body")
  | _ -> fail "bad formula"

let property e n p =
  let d = find e.definitions n in
  match List.assoc_opt p (pairs (get d "properties")) with
  | Some f -> f
  | None -> fail ("unknown property " ^ n ^ "." ^ p)

let closed e f =
  check_formula e f ;
  require (Names.is_empty (free_formula f)) "statement has free variables"

let record e name kind parameters properties =
  List.iter (fun (_, f) -> closed e f) properties ;
  let properties =
    List.sort (fun (a, _) (b, _) -> compare (utf16 a) (utf16 b)) properties
  in
  Hashtbl.replace e.definitions name
    (Obj
       [ ("kind", Str kind)
       ; ("parameters", strings parameters)
       ; ("properties", associations properties) ])

let add_axiom e name f =
  require
    (name <> "" && not (Hashtbl.mem e.axioms name || Hashtbl.mem e.theorems name))
    "duplicate axiom" ;
  closed e f ;
  Hashtbl.add e.axioms name f

let define_function e name params body =
  parameters params ;
  fresh_name e name ;
  check_term e body ;
  require
    ( (not (Names.mem name (functions body)))
    && Names.subset (free_term body) (names params) )
    "bad function body" ;
  Hashtbl.add e.functions name (Num (List.length params)) ;
  Hashtbl.add e.bodies name (Obj [("parameters", strings params); ("body", body)]) ;
  record e name "function" params
    [("equation", foralls params (eq (app name (List.map v params)) body))]

let define_predicate e name params body =
  parameters params ;
  fresh_name e name ;
  check_formula e body ;
  require
    ( (not (Names.mem name (symbols body)))
    && Names.subset (free_formula body) (names params) )
    "bad predicate body" ;
  Hashtbl.add e.predicates name (Num (List.length params)) ;
  record e name "predicate" params
    [("equation", foralls params (iff (pred name (List.map v params)) body))]
