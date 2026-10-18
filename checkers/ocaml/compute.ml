(* Exact arithmetic and checked equation evaluation.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Logic

(* Natural subtraction is truncated; Zarith subtraction itself is signed. *)
let truncated_sub a b = Z.max Z.zero (Z.sub a b)

(* Keep the evaluator's allocation limit, now measured directly in bits. *)
let multiply a b =
  require (Z.numbits a + Z.numbits b <= 3321928) "arithmetic bit limit" ;
  Z.mul a b

let bounded_int n limit =
  require (Z.sign n >= 0 && Z.leq n (Z.of_int limit)) "computation fuel exhausted" ;
  Z.to_int n

let lookup xs k =
  match List.assoc_opt k xs with
  | Some x -> x
  | None -> fail ("unknown computational definition " ^ k)

let sorted xs = List.sort_uniq (fun a b -> compare (utf16 a) (utf16 b)) xs

let bind n = Obj [("tag", Str "bind"); ("name", Str n)]

let ctor n args = Obj [("tag", Str "ctor"); ("name", Str n); ("args", Arr args)]

let matches_equation actual (patterns, body) =
  canonical (get actual "patterns") = canonical (Arr patterns)
  && term_json [] (get actual "body") = body

(* Steps of ground evaluation one computation may spend; `--fuel` sets it. *)
let default_fuel = ref 1000000

let evaluator env allowed =
  let recursive = pairs (get env "recursiveFunctions")
  and bodies = pairs (get env "functionBodies") in
  let used = Hashtbl.create 16
  and memo = Hashtbl.create 128
  and classifications = Hashtbl.create 16
  and prefixes = Hashtbl.create 128 in
  let fuel = ref !default_fuel in
  let spend () =
    decr fuel ;
    require (!fuel >= 0) "ground evaluation exhausted its fuel"
  in
  let note names = List.iter (fun n -> Hashtbl.replace used n ()) names in
  let exact_at decreasing name params equations =
    List.mem name allowed
    &&
    match List.assoc_opt name recursive with
    | None -> false
    | Some r ->
        optional r "admission" Null = Str "structural"
        && get r "parameters" = Arr (List.map (fun x -> Str x) params)
        && num (get r "decreasingParameter") = decreasing
        &&
        let es = arr (get r "equations") in
        List.length es = List.length equations
        && List.for_all2 matches_equation es equations
  in
  let exact name params equations = exact_at 0 name params equations in
  (* An explicit (non-recursive) definition admitted with exactly this body. *)
  let exact_body name params body =
    List.mem name allowed
    &&
    match List.assoc_opt name bodies with
    | None -> false
    | Some b ->
        get b "parameters" = Arr (List.map (fun x -> Str x) params)
        && term_json [] (get b "body") = body
  in
  let decision name =
    let nm = "Grace.Cumulus.Nat.Mod."
    and nr = "Grace.Core.Nat.Rec."
    and bo = "Grace.Core.Data.BoolOps."
    and bt = "Grace.Core.Data.Bool."
    and rat = "Grace.Cumulus.Rat.Computable.RationalCellOps." in
    let zero = ctor "zero" [] and s n = ctor "succ" [bind n] in
    let call n xs = App (n, xs) and v n = V n in
    let iz n = call (nm ^ "isZero") [v n] and pr n = call (nr ^ "predecessor") [v n] in
    let nz n = call (bo ^ "not") [iz n] in
    let minus = name = rat ^ "minus"
    and equal = name = nm ^ "equalNat"
    and less = name = rat ^ "less" in
    if not (minus || equal || less) then None
    else
      let helpers =
        exact (nm ^ "isZero") ["n"]
          [([zero], call (bt ^ "true") []); ([s "n"], call (bt ^ "false") [])]
        && exact (nr ^ "predecessor") ["n"] [([zero], N Z.zero); ([s "n"], v "n")]
      in
      let logical =
        if minus then
          exact (nm ^ "chooseNat") ["condition"; "yes"; "no"]
            [ ([ctor (bt ^ "false") []; bind "yes"; bind "no"], v "no")
            ; ([ctor (bt ^ "true") []; bind "yes"; bind "no"], v "yes") ]
        else
          exact (bo ^ "not") ["b"]
            [ ([ctor (bt ^ "false") []], call (bt ^ "true") [])
            ; ([ctor (bt ^ "true") []], call (bt ^ "false") []) ]
          && exact (bo ^ "and") ["a"; "b"]
               [ ([ctor (bt ^ "false") []; bind "b"], call (bt ^ "false") [])
               ; ([ctor (bt ^ "true") []; bind "b"], v "b") ]
      in
      let a, b = if equal then ("m", "n") else ("a", "b") in
      let base = if minus then N Z.zero else if equal then iz b else nz b in
      let recurse = call name [v a; pr b] in
      let step =
        if minus then call (nm ^ "chooseNat") [iz b; app "succ" [v a]; recurse]
        else call (bo ^ "and") [nz b; recurse]
      in
      if
        helpers && logical
        && exact name [a; b] [([zero; bind b], base); ([s a; bind b], step)]
      then
        Some
          ( (if minus then "minus" else if equal then "equal" else "less")
          , if minus then [nm ^ "isZero"; nr ^ "predecessor"; nm ^ "chooseNat"; name]
            else [nm ^ "isZero"; nr ^ "predecessor"; bo ^ "not"; bo ^ "and"; name] )
      else None
  in
  (* The descent-by-ones natural operators (predecessor, truncated subtraction,
     remainder, quotient) recognized exactly from their admitted equations and
     helper equations, each with a fixed dependency list recorded whatever the
     arguments are. *)
  let shortcuts = Hashtbl.create 16 in
  let shortcut name =
    match Hashtbl.find_opt shortcuts name with
    | Some c -> c
    | None ->
        let nm = "Grace.Cumulus.Nat.Mod."
        and nr = "Grace.Core.Nat.Rec."
        and ns = "Grace.Cumulus.Nat.Subtraction."
        and nd = "Grace.Cumulus.Nat.Division."
        and bo = "Grace.Core.Data.BoolOps."
        and bt = "Grace.Core.Data.Bool." in
        (* The remainder's fixed dependency list: its own equations, the helper
           equations, and the equality decision with the helpers that one names. *)
        let mod_definitions =
          [ nm ^ "mod"; nm ^ "nextRemainder"; nm ^ "chooseNat"; nm ^ "equalNat"
          ; nm ^ "isZero"; nr ^ "predecessor"; bo ^ "not"; bo ^ "and" ]
        in
        let operation =
          if name = nr ^ "predecessor" then Some ("predecessor", [nr ^ "predecessor"])
          else if name = ns ^ "sub" then Some ("sub", [ns ^ "sub"; nr ^ "predecessor"])
          else if name = nm ^ "mod" then Some ("mod", mod_definitions)
          else if name = nd ^ "quotientNat" then
            Some ("quotient", (nd ^ "quotientNat") :: mod_definitions)
          else None
        in
        let result =
          match operation with
          | Some (op, deps) when List.for_all (fun d -> List.mem d allowed) deps ->
              let zero = ctor "zero" [] and s n = ctor "succ" [bind n] in
              let call n xs = App (n, xs) and v n = V n in
              let predecessor_exact =
                exact (nr ^ "predecessor") ["n"] [([zero], N Z.zero); ([s "n"], v "n")]
              in
              (* The remainder equations, shared by the quotient. *)
              let remainder n d = call (nm ^ "mod") [v n; v d] in
              let mod_exact () =
                decision (nm ^ "equalNat") <> None
                && exact (nm ^ "chooseNat") ["condition"; "yes"; "no"]
                     [ ([ctor (bt ^ "false") []; bind "yes"; bind "no"], v "no")
                     ; ([ctor (bt ^ "true") []; bind "yes"; bind "no"], v "yes") ]
                && exact_body (nm ^ "nextRemainder") ["d"; "r"]
                     (call (nm ^ "chooseNat")
                        [ call (nm ^ "equalNat") [app "succ" [v "r"]; v "d"]
                        ; N Z.zero
                        ; app "succ" [v "r"] ] )
                && exact (nm ^ "mod") ["n"; "d"]
                     [ ([zero; bind "d"], N Z.zero)
                     ; ( [s "n"; bind "d"]
                       , call (nm ^ "nextRemainder") [v "d"; remainder "n" "d"] ) ]
              in
              let recognized =
                match op with
                | "predecessor" -> predecessor_exact
                | "sub" ->
                    predecessor_exact
                    && exact_at 1 (ns ^ "sub") ["m"; "n"]
                         [ ([bind "m"; zero], v "m")
                         ; ( [bind "m"; s "n"]
                           , call (nr ^ "predecessor") [call (ns ^ "sub") [v "m"; v "n"]] )
                         ]
                | "mod" -> mod_exact ()
                | _ ->
                    mod_exact ()
                    && exact (nd ^ "quotientNat") ["n"; "d"]
                         [ ([zero; bind "d"], N Z.zero)
                         ; ( [s "n"; bind "d"]
                           , call (nm ^ "chooseNat")
                               [ call (nm ^ "equalNat") [app "succ" [remainder "n" "d"]; v "d"]
                               ; app "succ" [call (nd ^ "quotientNat") [v "n"; v "d"]]
                               ; call (nd ^ "quotientNat") [v "n"; v "d"] ] ) ]
              in
              if recognized then Some (op, deps) else None
          | _ -> None
        in
        Hashtbl.replace shortcuts name result ;
        result
  in
  let rec classify visiting name =
    match Hashtbl.find_opt classifications name with
    | Some c -> c
    | None ->
        if List.mem name visiting || not (List.mem name allowed) then None
        else
          let result =
            match List.assoc_opt name recursive with
            | None -> None
            | Some r -> (
                let es = arr (get r "equations")
                and params = arr (get r "parameters") in
                let pos = num (get r "decreasingParameter") in
                if List.length es <> 2 || pos < 0 || pos >= List.length params then
                  None
                else
                  let equation root =
                    List.find_opt
                      (fun e ->
                        let ps = arr (get e "patterns") in
                        List.length ps = List.length params
                        &&
                        let p = nth ps pos in
                        optional p "tag" Null = Str "ctor"
                        && optional p "name" Null = Str root )
                      es
                  in
                  match (equation "zero", equation "succ") with
                  | Some z, Some s -> (
                      let zp = arr (get z "patterns")
                      and sp = arr (get s "patterns") in
                      let root = nth sp pos in
                      let fields = arr (get root "args") in
                      if
                        arr (get (nth zp pos) "args") <> []
                        || List.length fields <> 1
                        || optional (List.hd fields) "tag" Null <> Str "bind"
                      then None
                      else
                        let predecessor = str (get (List.hd fields) "name") in
                        let regular ps =
                          List.for_all
                            (fun (i, p) ->
                              i = pos || optional p "tag" Null = Str "bind" )
                            (List.mapi (fun i p -> (i, p)) ps)
                        in
                        if not (regular zp && regular sp) then None
                        else
                          let args =
                            List.mapi
                              (fun i p ->
                                V (if i = pos then predecessor else str (get p "name"))
                                )
                              sp
                          in
                          let call = App (name, args)
                          and zb = term_json [] (get z "body")
                          and sb = term_json [] (get s "body") in
                          let other ps body =
                            List.exists
                              (fun (i, p) -> i <> pos && body = V (str (get p "name")))
                              (List.mapi (fun i p -> (i, p)) ps)
                          in
                          if
                            List.length params = 2
                            && other zp zb
                            && sb = app "succ" [call]
                          then Some ("add", [name])
                          else
                            match sb with
                            | App (fn, [a; b]) -> (
                              match classify (name :: visiting) fn with
                              | Some ("add", deps)
                                when List.length params = 2
                                     && zb = N Z.zero
                                     && ( (a = call && other sp b)
                                        || (b = call && other sp a) ) ->
                                  Some ("mul", sorted (name :: deps))
                              | Some ("mul", deps)
                                when List.length params = 1
                                     && zb = N Z.one
                                     && ( (a = call && b = app "succ" [V predecessor])
                                        || (b = call && a = app "succ" [V predecessor])
                                        ) ->
                                  Some ("factorial", sorted (name :: deps))
                              | _ -> None )
                            | _ -> None )
                  | _ -> None )
          in
          Hashtbl.replace classifications name result ;
          result
  in
  let rec pattern bindings pat value =
    match str (get pat "tag") with
    | "bind" -> (
        let n = str (get pat "name") in
        match List.assoc_opt n !bindings with
        | Some old -> old = value
        | None ->
            bindings := (n, value) :: !bindings ;
            true )
    | "ctor" -> (
        let name = str (get pat "name") and ps = arr (get pat "args") in
        match (name, ps, value) with
        | "zero", [], N n when Z.equal n Z.zero -> true
        | "succ", [p], N n when Z.sign n > 0 -> pattern bindings p (N (Z.pred n))
        | _, _, App (fn, args) when fn = name && List.length ps = List.length args ->
            List.for_all2 (pattern bindings) ps args
        | _ -> false )
    | _ -> fail "bad computation pattern"
  in
  let rec evaluate bindings override term =
    spend () ;
    match term with
    | N _ -> term
    | V n -> (
      match List.assoc_opt n bindings with
      | Some v -> v
      | None -> fail ("free variable in ground computation " ^ n) )
    | B _ -> fail "bound index in ground computation"
    | App (fn, args) -> invoke override fn (List.map (evaluate bindings override) args)
  and invoke override fn args =
    spend () ;
    let key = (fn, args) in
    match (fn, args, override) with
    | "zero", [], _ -> N Z.zero
    | "succ", [N n], _ -> N (Z.succ n)
    | _, _, Some (k, v) when k = key -> v
    | _ -> (
      match Hashtbl.find_opt memo key with
      | Some v -> v
      | None ->
          let recdef =
            if List.mem fn allowed then List.assoc_opt fn recursive else None
          in
          let result =
            match recdef with
            | Some r -> (
                let fast =
                  match (args, decision fn) with
                  | [N a; N b], Some (op, deps) ->
                      note deps ;
                      Some
                        ( if op = "minus" then N (truncated_sub a b)
                        else
                          App
                            ( ( "Grace.Core.Data.Bool."
                              ^
                              if
                                if op = "equal" then Z.equal a b else Z.compare a b < 0
                              then "true"
                              else "false" )
                            , [] ) )
                  | _ -> (
                    match (shortcut fn, args) with
                    | Some ("predecessor", deps), [N a] ->
                        note deps ;
                        Some (N (if Z.sign a > 0 then Z.pred a else Z.zero))
                    | Some ("sub", deps), [N a; N b] ->
                        note deps ;
                        Some (N (truncated_sub a b))
                    (* The remainder by zero never wraps, so n % 0 = n; the
                       quotient by zero is zero. *)
                    | Some ("mod", deps), [N a; N b] ->
                        note deps ;
                        Some (N (if Z.sign b = 0 then a else Z.rem a b))
                    | Some ("quotient", deps), [N a; N b] ->
                        note deps ;
                        Some (N (if Z.sign b = 0 then Z.zero else Z.div a b))
                    | _ -> (
                      match (classify [] fn, args) with
                      | Some ("add", deps), [N a; N b] ->
                          note deps ;
                          Some (N (Z.add a b))
                      | Some ("mul", deps), [N a; N b] ->
                          note deps ;
                          Some (N (multiply a b))
                      | Some ("factorial", deps), [N n] ->
                          note deps ;
                          let count = bounded_int n !fuel in
                          let value = ref Z.one in
                          for i = 2 to count do
                            spend () ;
                            value := multiply !value (Z.of_int i)
                          done ;
                          Some (N !value)
                      | _ -> None ) )
                in
                match fast with
                | Some v -> v
                | None -> (
                    let equations = arr (get r "equations") in
                    let matched values =
                      List.find_map
                        (fun e ->
                          let ps = arr (get e "patterns") in
                          require
                            (List.length ps = List.length values)
                            "recursive arity" ;
                          let bindings = ref [] in
                          if List.for_all2 (pattern bindings) ps values then
                            Some (e, !bindings)
                          else None )
                        equations
                    in
                    (* Iterating primitive Nat recursion avoids host-stack growth. The override
        replaces only the exact preceding call at the preceding argument tuple. *)
                    let pos = num (get r "decreasingParameter") in
                    let primitive =
                      match nth args pos with
                      | N n -> (
                          let zero =
                            List.mapi (fun i x -> if i = pos then N Z.zero else x) args
                          in
                          match matched zero with
                          | None -> None
                          | Some (e, b) ->
                              let count = bounded_int n !fuel in
                              let prefix_key = (fn, zero) in
                              let start, initial =
                                match Hashtbl.find_opt prefixes prefix_key with
                                | Some (index, value) when index <= count ->
                                    (index, value)
                                | _ ->
                                    let value =
                                      evaluate b override (term_json [] (get e "body"))
                                    in
                                    Hashtbl.replace memo prefix_key value ;
                                    (0, value)
                              in
                              let value = ref initial in
                              (* Retain exact evaluated prefixes for this fixed argument tuple. *)
                              for i = start to count - 1 do
                                let previous =
                                  List.mapi
                                    (fun j x -> if j = pos then N (Z.of_int i) else x)
                                    args
                                in
                                let next =
                                  List.mapi
                                    (fun j x ->
                                      if j = pos then N (Z.of_int (i + 1)) else x )
                                    args
                                in
                                match matched next with
                                | None -> fail "unmatched recursive constructor"
                                | Some (e, b) ->
                                    value :=
                                      evaluate b
                                        (Some ((fn, previous), !value))
                                        (term_json [] (get e "body")) ;
                                    Hashtbl.replace memo (fn, next) !value ;
                                    Hashtbl.replace prefixes prefix_key (i + 1, !value)
                              done ;
                              Some !value )
                      | _ -> None
                    in
                    match primitive with
                    | Some v ->
                        note [fn] ;
                        v
                    | None -> (
                      match matched args with
                      | Some (e, b) ->
                          note [fn] ;
                          evaluate b override (term_json [] (get e "body"))
                      | None -> App (fn, args) ) ) )
            | None -> (
              match if List.mem fn allowed then List.assoc_opt fn bodies else None with
              | Some body ->
                  let params = List.map str (arr (get body "parameters")) in
                  require (List.length params = List.length args) "function body arity" ;
                  note [fn] ;
                  evaluate (List.combine params args) override
                    (term_json [] (get body "body"))
              | None -> App (fn, args) )
          in
          Hashtbl.replace memo key result ;
          result )
  in
  ( (fun term -> evaluate [] None term)
  , fun () -> sorted (Hashtbl.fold (fun n () acc -> n :: acc) used []) )

let check env formula definitions =
  require
    (definitions = sorted definitions)
    "computation dependencies must be sorted and unique" ;
  let known =
    pairs (get env "functionBodies") @ pairs (get env "recursiveFunctions")
  in
  List.iter (fun n -> ignore (lookup known n)) definitions ;
  let left, right =
    match formula with
    | Eq (a, b) -> (a, b)
    | _ -> fail "computation requires equality"
  in
  let ev1, used1 = evaluator env definitions
  and ev2, used2 = evaluator env definitions in
  let a = ev1 left and b = ev2 right in
  require (a = b) "different computed normal forms" ;
  require
    (sorted (used1 () @ used2 ()) = definitions)
    "inexact computation dependencies"

let rational env formula =
  let cls = "Grace.Cumulus.Rat.Operations.rationalClass"
  and add = "Grace.Core.Nat.Rec.add"
  and mul = "Grace.Core.Nat.Rec.mul" in
  let left, right =
    match formula with
    | Eq (App (l, [N a; N b; N m]), App (r, [N c; N d; N n]))
      when l = cls && r = cls && Z.sign m > 0 && Z.sign n > 0 ->
        ([N a; N b; N m], [N c; N d; N n])
    | _ -> fail "rational computation needs natural classes with positive denominators"
  in
  require
    (List.mem_assoc "Naturals" (pairs (get env "datatypes")))
    "rational computation requires Naturals" ;
  let cross first second =
    match (first, second) with
    | [a; b; m], [c; d; n] ->
        Eq
          ( App (add, [App (mul, [n; a]); App (mul, [m; d])])
          , App (add, [App (mul, [m; c]); App (mul, [n; b])]) )
    | _ -> assert false
  in
  let names = ["a"; "b"; "m"; "c"; "d"; "n"] in
  let vars = List.map (fun n -> V n) names in
  let a = List.filteri (fun i _ -> i < 3) vars
  and b = List.filteri (fun i _ -> i >= 3) vars in
  let premises =
    List.map (fun x -> Pred ("Nat", [x])) vars
    @ [Imp (Eq (V "m", N Z.zero), False); Imp (Eq (V "n", N Z.zero), False); cross a b]
  in
  let schema =
    List.fold_right
      (fun n body -> All (abstract n body))
      names
      (List.fold_right
         (fun p body -> Imp (p, body))
         premises
         (Eq (App (cls, a), App (cls, b))))
  in
  let theorem = lookup (pairs (get env "theorems")) (cls ^ ".eq") in
  require
    (formula_json [] theorem = schema)
    "rational computation requires proved quotient criterion" ;
  check env (cross left right) [add; mul]
