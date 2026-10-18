(* Every supported conservative declaration operation.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Named
open Environment

let list_strings j = List.map str (arr j)

let within actual allowed =
  require (Names.subset actual (names allowed)) "undeclared declaration variable"

let enabled e k =
  require (get e.capabilities k = Bool true) ("foundation disables " ^ k)

let constructor e name =
  let found = ref None in
  Hashtbl.iter
    (fun _ d ->
      List.iter
        (fun c -> if str (get c "name") = name then found := Some c)
        (arr (get d "constructors")) )
    e.datatypes ;
  match !found with Some c -> c | None -> fail ("unknown constructor " ^ name)

let define_subset e p =
  enabled e "separation" ;
  let name = str (get p "name")
  and ps = list_strings (get p "parameters")
  and x = str (get p "element")
  and bound = get p "bound"
  and condition = get p "condition" in
  parameters ps ;
  fresh_name e name ;
  check_term e bound ;
  check_formula e condition ;
  require (x <> "" && not (List.mem x ps)) "bad Separation element" ;
  within (free_term bound) ps ;
  within (free_formula condition) (x :: ps) ;
  Hashtbl.add e.functions name (Num (List.length ps)) ;
  record e name "separation" ps
    [ ( "membership"
      , foralls
          (ps @ [x])
          (iff
             (pred "in" [v x; app name (List.map v ps)])
             (conj (pred "in" [v x; bound]) condition)) ) ]

let declare_datatype e spec =
  enabled e "inductiveDefinitions" ;
  let name = str (get spec "name")
  and predicate = str (get spec "predicate")
  and cs = arr (get spec "constructors")
  and ps = list_strings (optional spec "parameters" (Arr [])) in
  require (cs <> []) "empty datatype" ;
  let encoding = get spec "setTheoreticEncoding" in
  require (encoding = Bool true || encoding = Bool false) "bad datatype encoding" ;
  parameters ps ;
  fresh_name e name ;
  fresh_name e predicate ;
  require (not (Hashtbl.mem e.datatypes name)) "duplicate datatype" ;
  if encoding = Bool true then
    require
      ( find e.functions "orderedPair" = Num 2
      && find e.functions "empty" = Num 0
      && Hashtbl.mem e.datatypes "Naturals" )
      "datatype encoding prerequisites" ;
  Logic.unique (List.map (fun c -> str (get c "name")) cs) ;
  List.iter
    (fun c ->
      let n = str (get c "name") and arity = num (get c "arity") in
      fresh_name e n ;
      require (arity >= 0) "bad constructor arity" ;
      let recursive = List.map num (arr (get c "recursiveFields"))
      and fields = arr (optional c "parameterFields" (Arr [])) in
      Logic.unique recursive ;
      List.iter
        (fun i -> require (i >= 0 && i < arity) "recursive field out of range")
        recursive ;
      Logic.unique (List.map (fun f -> num (get f "field")) fields) ;
      List.iter
        (fun f ->
          let i = num (get f "field") and p = num (get f "parameter") in
          require
            ( i >= 0 && i < arity && p >= 0
            && p < List.length ps
            && not (List.mem i recursive) )
            "parameter field out of range" )
        fields )
    cs ;
  Hashtbl.add e.predicates predicate (Num (List.length ps + 1)) ;
  List.iter (fun c -> Hashtbl.add e.functions (str (get c "name")) (get c "arity")) cs ;
  let fresh_fields prefix count =
    let used = ref (names ps) in
    List.init count (fun i ->
        let rec loop n = if Names.mem n !used then loop ("_" ^ n) else n in
        let n = loop (prefix ^ string_of_int i) in
        used := Names.add n !used ;
        n )
  in
  let combine op = function
    | [] -> fail "empty connective"
    | x :: xs -> List.fold_left op x xs
  in
  let sequence xs =
    List.fold_right (fun x tail -> app "orderedPair" [x; tail]) xs (app "empty" [])
  in
  let local n = List.hd (List.rev (String.split_on_char '.' n)) in
  let props = ref [] in
  let add n p = props := (n, p) :: !props in
  let guards ctor ts =
    List.concat
      (List.mapi
         (fun i t ->
           if List.mem (Num i) (arr (get ctor "recursiveFields")) then
             [pred predicate (List.map v ps @ [t])]
           else
             List.filter_map
               (fun f ->
                 if num (get f "field") = i then
                   Some (pred "in" [t; v (Logic.nth ps (num (get f "parameter")))])
                 else None )
               (arr (optional ctor "parameterFields" (Arr []))) )
         ts)
  in
  List.iter
    (fun c ->
      let n = str (get c "name") and arity = num (get c "arity") in
      let fields = List.init arity (fun i -> "field" ^ string_of_int i) in
      let ts = List.map v fields in
      let closure =
        List.fold_right imp (guards c ts) (pred predicate (List.map v ps @ [app n ts]))
      in
      add ("constructor." ^ local n) (foralls (ps @ fields) closure) ;
      ( if encoding = Bool true then
        let tag =
          sequence
            (List.map (fun cp -> nat (string_of_int cp)) (utf8 (name ^ "." ^ n)))
        in
        add
          ("representation." ^ local n)
          (foralls (ps @ fields) (eq (app n ts) (app "orderedPair" [tag; sequence ts])))
      ) ;
      if arity > 0 then
        let l = fresh_fields "left" arity and r = fresh_fields "right" arity in
        add
          ("injective." ^ local n)
          (foralls (l @ r)
             (imp
                (eq (app n (List.map v l)) (app n (List.map v r)))
                (combine conj (List.map2 (fun x y -> eq (v x) (v y)) l r)))) )
    cs ;
  List.iteri
    (fun i l ->
      List.iteri
        (fun j r ->
          if j > i then
            let ls = fresh_fields "left" (num (get l "arity"))
            and rs = fresh_fields "right" (num (get r "arity")) in
            add
              ( "disjoint."
              ^ local (str (get l "name"))
              ^ "."
              ^ local (str (get r "name")) )
              (foralls (ls @ rs)
                 (neg
                    (eq
                       (app (str (get l "name")) (List.map v ls))
                       (app (str (get r "name")) (List.map v rs))))) )
        cs )
    cs ;
  let element = if List.mem "value" ps then "_value" else "value" in
  let alternatives =
    List.mapi
      (fun i c ->
        let fields =
          fresh_fields ("case" ^ string_of_int i ^ "_field") (num (get c "arity"))
        in
        let ts = List.map v fields in
        List.fold_right exists fields
          (combine conj (guards c ts @ [eq (v element) (app (str (get c "name")) ts)]))
        )
      cs
  in
  add "cases"
    (foralls
       (ps @ [element])
       (imp (pred predicate (List.map v ps @ [v element])) (combine disj alternatives))) ;
  Hashtbl.add e.datatypes name spec ;
  record e name "datatype" [] !props

let register_naturals e =
  require (not (Hashtbl.mem e.datatypes "Naturals")) "duplicate Naturals" ;
  let successor = app "union" [app "pair" [v "n"; app "pair" [v "n"; v "n"]]] in
  let expected =
    forall "n" (iff (pred "Nat" [v "n"]) (pred "in" [v "n"; app "omega" []]))
  in
  let minimality =
    forall "A"
      (imp
         (conj
            (pred "in" [app "empty" []; v "A"])
            (forall "n" (imp (pred "in" [v "n"; v "A"]) (pred "in" [successor; v "A"]))))
         (forall "n"
            (imp (pred "in" [v "n"; app "omega" []]) (pred "in" [v "n"; v "A"]))))
  in
  require
    ( canonical (find e.bodies "zero")
      = canonical (Obj [("parameters", Arr []); ("body", app "empty" [])])
    && canonical (find e.bodies "succ")
       = canonical (Obj [("parameters", strings ["n"]); ("body", successor)])
    && same_formula (property e "Nat" "equation") expected
    && same_formula (find e.axioms "set.infinity.minimal") minimality )
    "noncanonical Nat registration" ;
  Hashtbl.add e.datatypes "Naturals"
    (Obj
       [ ("name", Str "Naturals")
       ; ("predicate", Str "Nat")
       ; ( "constructors"
         , Arr
             [ Obj [("name", Str "zero"); ("arity", Num 0); ("recursiveFields", Arr [])]
             ; Obj
                 [ ("name", Str "succ")
                 ; ("arity", Num 1)
                 ; ("recursiveFields", Arr [Num 0]) ] ] ) ])

let rec check_pattern e p =
  match tag p with
  | "bind" -> require (str (get p "name") <> "") "empty pattern binder"
  | "ctor" ->
      let c = constructor e (str (get p "name")) in
      let args = arr (get p "args") in
      require (List.length args = num (get c "arity")) "bad constructor pattern" ;
      List.iter (check_pattern e) args
  | _ -> fail "bad pattern"

let define_structural e o =
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and datatype = str (get o "datatype")
  and pos = num (get o "decreasingParameter")
  and equations = arr (get o "equations") in
  fresh_name e name ;
  parameters ps ;
  let data = find e.datatypes datatype in
  let cs = arr (get data "constructors") in
  require
    (pos >= 0 && pos < List.length ps && List.length equations = List.length cs)
    "malformed structural recursion" ;
  let seen = ref [] in
  let properties =
    List.mapi
      (fun i equation ->
        let patterns = arr (get equation "patterns") and body = get equation "body" in
        require
          ( List.length patterns = List.length ps
          && List.for_all
               (fun (i, p) -> i = pos || tag p = "bind")
               (List.mapi (fun i p -> (i, p)) patterns) )
          "recursive pattern layout" ;
        let root = Logic.nth patterns pos in
        require (tag root = "ctor") "expected constructor root" ;
        let root_name = str (get root "name") in
        let ctor =
          try List.find (fun c -> str (get c "name") = root_name) cs
          with Not_found -> fail "wrong recursive constructor"
        in
        require
          ( (not (List.mem root_name !seen))
          && List.length (arr (get root "args")) = num (get ctor "arity") )
          "constructor coverage" ;
        seen := root_name :: !seen ;
        List.iter (check_pattern e) patterns ;
        let bindings = List.concat_map pattern_bindings patterns in
        parameters bindings ;
        within (free_term body) bindings ;
        let smaller =
          List.concat_map
            (fun i -> pattern_bindings (Logic.nth (arr (get root "args")) (num i)))
            (arr (get ctor "recursiveFields"))
        in
        let rec check t =
          match tag t with
          | "var" | "nat" -> check_term e t
          | "app" ->
              let fn = str (get t "fn") and args = arr (get t "args") in
              if fn = name then (
                require (List.length args = List.length ps) "recursive arity" ;
                let dec = Logic.nth args pos in
                require
                  (tag dec = "var" && List.mem (str (get dec "name")) smaller)
                  "nondecreasing recursive call" )
              else
                require
                  (find e.functions fn = Num (List.length args))
                  "unknown recursive-body function" ;
              List.iter check args
          | _ -> fail "bad recursive body"
        in
        check body ;
        ( "equation." ^ string_of_int i
        , foralls bindings (eq (app name (List.map pattern_term patterns)) body) ) )
      equations
  in
  Hashtbl.add e.functions name (Num (List.length ps)) ;
  Hashtbl.add e.recursive name
    (Obj
       [ ("name", Str name)
       ; ("parameters", strings ps)
       ; ("datatype", Str datatype)
       ; ("decreasingParameter", Num pos)
       ; ("equations", Arr equations)
       ; ("admission", Str "structural") ]) ;
  record e name "recursive" ps properties

let define_replacement e o =
  enabled e "replacement" ;
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and domain = get o "domain"
  and input = str (get o "input")
  and output = str (get o "output")
  and relation = get o "relation" in
  parameters ps ;
  fresh_name e name ;
  check_term e domain ;
  check_formula e relation ;
  require
    ( input <> "" && output <> "" && input <> output
    && not
         ( List.mem input ps || List.mem output ps
         || Names.mem name (functions domain)
         || Names.mem name (symbols relation) ) )
    "bad Replacement variables" ;
  within (free_term domain) ps ;
  within (free_formula relation) (input :: output :: ps) ;
  let forbidden =
    Names.union (names (input :: output :: ps)) (free_formula relation)
  in
  let other = fresh (output ^ "_other") forbidden in
  let at_other = subst_formula relation output (v other) in
  let expected =
    foralls ps
      (forall input
         (imp
            (pred "in" [v input; domain])
            (exists output
               (conj relation (forall other (imp at_other (eq (v other) (v output))))))))
  in
  Ast_proof.expect e (get o "functionality") expected ;
  Hashtbl.add e.functions name (Num (List.length ps)) ;
  let member = fresh "member" forbidden in
  let membership =
    foralls
      (ps @ [member])
      (iff
         (pred "in" [v member; app name (List.map v ps)])
         (exists input
            (conj
               (pred "in" [v input; domain])
               (subst_formula relation output (v member)))))
  in
  record e name "replacement" ps
    [("functionality", expected); ("membership", membership)]

let require_recursion e =
  enabled e "separation" ;
  enabled e "replacement" ;
  require (Hashtbl.mem e.axioms "set.foundation") "missing Foundation axiom"

let define_membership e o =
  require_recursion e ;
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and x = str (get o "variable")
  and y = str (get o "predecessor")
  and h = str (get o "history")
  and step = get o "step" in
  fresh_name e name ;
  fresh_name e (name ^ ".history") ;
  parameters (ps @ [x; y; h]) ;
  check_term e step ;
  within (free_term step) (ps @ [x; h]) ;
  Hashtbl.add e.functions name (Num (List.length ps + 1)) ;
  Hashtbl.add e.functions (name ^ ".history") (Num (List.length ps + 1)) ;
  let pair = fresh "pair" (names (ps @ [x; y; h])) in
  let history = app (name ^ ".history") (List.map v ps @ [v x]) in
  let value n = app name (List.map v ps @ [v n]) in
  let membership =
    foralls
      (ps @ [x; pair])
      (iff
         (pred "in" [v pair; history])
         (exists y
            (conj
               (pred "in" [v y; v x])
               (eq (v pair) (app "orderedPair" [v y; value y])))))
  in
  record e name "membership-recursive"
    (ps @ [x])
    [ ("history.membership", membership)
    ; ("equation", foralls (ps @ [x]) (eq (value x) (subst_term step h history))) ]

(* Definitional normalization for the ordinal-interface obligations. *)
let rec normalize e fuel term =
  require (fuel > 0) "normalization fuel exhausted" ;
  if tag term <> "app" then term
  else
    let fn = str (get term "fn") in
    let args = List.map (normalize e (fuel - 1)) (arr (get term "args")) in
    let is_ctor =
      try
        ignore (constructor e fn) ;
        true
      with Reject _ -> false
    in
    match if is_ctor then None else Hashtbl.find_opt e.bodies fn with
    | None -> app fn args
    | Some body ->
        let ps = list_strings (get body "parameters") in
        require (List.length ps = List.length args) "normalization arity" ;
        normalize e (fuel - 1) (subst_many (get body "body") (List.combine ps args))

let rec expand e fuel formula =
  require (fuel > 0) "expansion fuel exhausted" ;
  match tag formula with
  | "bottom" -> formula
  | "eq" ->
      eq
        (normalize e 10000 (get formula "left"))
        (normalize e 10000 (get formula "right"))
  | "pred" -> (
      let name = str (get formula "pred") and args = arr (get formula "args") in
      let equation =
        match Hashtbl.find_opt e.definitions name with
        | Some d when get d "kind" = Str "predicate" ->
            List.assoc_opt "equation" (pairs (get d "properties"))
        | _ -> None
      in
      let instance =
        match equation with
        | None -> None
        | Some equation ->
            let rec peel ps f =
              if tag f = "forall" then
                peel (ps @ [str (get f "variable")]) (get f "body")
              else (ps, f)
            in
            let ps, body = peel [] equation in
            if tag body <> "iff" || List.length ps <> List.length args then None
            else
              let left = get body "left" and right = get body "right" in
              let matches f = tag f = "pred" && str (get f "pred") = name in
              let body =
                if matches left then Some right
                else if matches right then Some left
                else None
              in
              Option.map
                (fun f ->
                  List.fold_left
                    (fun f (p, t) -> subst_formula f p t)
                    f (List.combine ps args) )
                body
      in
      match instance with
      | Some f -> expand e (fuel - 1) f
      | None -> pred name (List.map (normalize e 10000) args) )
  | ("imp" | "and" | "or" | "iff") as k ->
      binary k
        (expand e (fuel - 1) (get formula "left"))
        (expand e (fuel - 1) (get formula "right"))
  | ("forall" | "exists") as k ->
      quantify k
        (str (get formula "variable"))
        (expand e (fuel - 1) (get formula "body"))
  | _ -> fail "bad expanded formula"

let transitive term =
  let member = fresh "member" (free_term term) in
  let element = fresh "element" (Names.add member (free_term term)) in
  forall member
    (imp
       (pred "in" [v member; term])
       (forall element
          (imp (pred "in" [v element; v member]) (pred "in" [v element; term]))))

let ordinal term =
  let member = fresh "ordinalMember" (free_term term) in
  conj (transitive term)
    (forall member (imp (pred "in" [v member; term]) (transitive (v member))))

let limit_ordinal term successor =
  let member = fresh "limitMember" (free_term term) in
  conj (ordinal term)
    (conj
       (neg (eq term (app "empty" [])))
       (forall member
          (imp (pred "in" [v member; term]) (pred "in" [successor (v member); term]))))

let define_transfinite e o =
  require_recursion e ;
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and x = str (get o "ordinal")
  and y = str (get o "predecessor")
  and h = str (get o "history") in
  let zero = get o "zero"
  and successor = get o "successor"
  and limit = get o "limit" in
  fresh_name e name ;
  fresh_name e (name ^ ".history") ;
  parameters (ps @ [x; y; h]) ;
  let arity = List.length ps + 1 in
  Hashtbl.add e.functions name (Num arity) ;
  List.iter (check_term e) [zero; successor; limit] ;
  within (free_term zero) ps ;
  within (free_term successor) (ps @ [y]) ;
  within (free_term limit) (ps @ [x; h]) ;
  let rec calls t =
    if tag t <> "app" then []
    else
      let children = List.concat_map calls (arr (get t "args")) in
      if str (get t "fn") = name then t :: children else children
  in
  require (calls zero = [] && calls limit = []) "recursion outside successor clause" ;
  let expected = List.map v ps @ [v y] in
  List.iter
    (fun t ->
      let args = arr (get t "args") in
      require
        (List.length args = arity && List.for_all2 same_term args expected)
        "non-predecessor recursive call" )
    (calls successor) ;
  let index = optional o "successorIndex" Null in
  if index <> Null then (
    let n = str index in
    require (find e.functions n = Num 1) "successor arity" ;
    let probe = v (fresh "ordinalProbe" (names (ps @ [x; y; h]))) in
    require
      (same_term
         (normalize e 10000 (app n [probe]))
         (normalize e 10000 (app "union2" [probe; app "singleton" [probe]])))
      "noncanonical ordinal successor" ) ;
  let next t =
    if index = Null then app "union2" [t; app "singleton" [t]] else app (str index) [t]
  in
  let ordinal_condition = optional o "ordinalCondition" Null
  and limit_condition = optional o "limitCondition" Null in
  let validate_condition condition canonical =
    if condition <> Null then (
      check_formula e condition ;
      within (free_formula condition) [x] ;
      require
        (same_formula (expand e 10000 condition) (expand e 10000 canonical))
        "noncanonical ordinal condition" )
  in
  validate_condition ordinal_condition (ordinal (v x)) ;
  validate_condition limit_condition (limit_ordinal (v x) next) ;
  let ord_at t =
    if ordinal_condition = Null then ordinal t else subst_formula ordinal_condition x t
  in
  let limit_at t =
    if limit_condition = Null then limit_ordinal t next
    else subst_formula limit_condition x t
  in
  Hashtbl.add e.functions (name ^ ".history") (Num arity) ;
  let pair = fresh "pair" (names (ps @ [x; y; h])) in
  let earlier = fresh "earlier" (names (ps @ [x; y; h; pair])) in
  let history = app (name ^ ".history") (List.map v ps @ [v x])
  and value t = app name (List.map v ps @ [t]) in
  let history_member =
    foralls
      (ps @ [x; pair])
      (iff
         (pred "in" [v pair; history])
         (exists earlier
            (conj
               (pred "in" [v earlier; v x])
               (eq (v pair) (app "orderedPair" [v earlier; value (v earlier)])))))
  in
  record e name "transfinite-recursive"
    (ps @ [x])
    [ ("history.membership", history_member)
    ; ("equation.zero", foralls ps (eq (value (nat "0")) zero))
    ; ( "equation.successor"
      , foralls (ps @ [y]) (imp (ord_at (v y)) (eq (value (next (v y))) successor)) )
    ; ( "equation.limit"
      , foralls
          (ps @ [x])
          (imp (limit_at (v x)) (eq (value (v x)) (subst_term limit h history))) )
    ; ( "outside"
      , foralls
          (ps @ [x])
          (imp (neg (ord_at (v x))) (eq (value (v x)) (app "empty" []))) ) ]

let define_well_founded_set e o =
  require_recursion e ;
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and x = str (get o "variable")
  and y = str (get o "predecessor")
  and h = str (get o "history") in
  let domain = get o "domain"
  and precedes = get o "precedes"
  and step = get o "step" in
  let solution = name ^ ".Solution" and history_name = name ^ ".history" in
  List.iter (fresh_name e) [name; solution; history_name] ;
  parameters (ps @ [x; y; h]) ;
  check_term e domain ;
  check_formula e precedes ;
  check_term e step ;
  within (free_term domain) ps ;
  within (free_formula precedes) (ps @ [y; x]) ;
  within (free_term step) (ps @ [x; h]) ;
  let forbidden =
    ref
      (Names.union
         (names (ps @ [x; y; h]))
         (Names.union (free_term domain)
            (Names.union (free_formula precedes) (free_term step))))
  in
  let new_name base =
    let n = fresh base !forbidden in
    forbidden := Names.add n !forbidden ;
    n
  in
  let subset = new_name "subset" in
  let minimum = new_name "minimum" in
  let member = new_name "member" in
  let graph = new_name "graph" in
  let other_graph = new_name "otherGraph" in
  let output = new_name "output" in
  let other_output = new_name "otherOutput" in
  let at_relation earlier later =
    subst_formula (subst_formula precedes y earlier) x later
  in
  let mem a b = pred "in" [a; b] in
  let pair a b = app "orderedPair" [a; b] in
  let domain_subset =
    forall member (imp (mem (v member) (v subset)) (mem (v member) domain))
  in
  let minimal =
    exists minimum
      (conj
         (mem (v minimum) (v subset))
         (forall y (imp (at_relation (v y) (v minimum)) (neg (mem (v y) (v subset))))))
  in
  let expected_wf =
    foralls ps
      (forall subset
         (imp domain_subset (imp (neg (eq (v subset) (app "empty" []))) minimal)))
  in
  Ast_proof.expect e (get o "wellFounded") expected_wf ;
  let history_formula graph_term point history_term =
    let pair_value = fresh "pairValue" !forbidden in
    let earlier = fresh "earlier" (Names.add pair_value !forbidden) in
    let earlier_value =
      fresh "earlierValue" (Names.add earlier (Names.add pair_value !forbidden))
    in
    let prior =
      exists earlier
        (exists earlier_value
           (conj
              (mem (v earlier) domain)
              (conj
                 (at_relation (v earlier) point)
                 (eq (v pair_value) (pair (v earlier) (v earlier_value))))))
    in
    forall pair_value
      (iff
         (mem (v pair_value) history_term)
         (conj (mem (v pair_value) graph_term) prior))
  in
  let graph_subset =
    forall member
      (imp
         (mem (v member) (v graph))
         (exists x
            (exists output
               (conj (mem (v x) domain) (eq (v member) (pair (v x) (v output)))))))
  in
  let graph_total =
    forall x
      (imp (mem (v x) domain) (exists output (mem (pair (v x) (v output)) (v graph))))
  in
  let graph_unique =
    forall x
      (imp
         (mem (v x) domain)
         (forall output
            (forall other_output
               (imp
                  (conj
                     (mem (pair (v x) (v output)) (v graph))
                     (mem (pair (v x) (v other_output)) (v graph)))
                  (eq (v output) (v other_output))))))
  in
  let graph_shape = conj graph_subset (conj graph_total graph_unique) in
  let instantiated_step = subst_many step [(x, v x); (h, v h)] in
  let step_equation =
    exists h
      (exists output
         (conj
            (history_formula (v graph) (v x) (v h))
            (conj
               (mem (pair (v x) (v output)) (v graph))
               (eq (v output) instantiated_step))))
  in
  let solution_body =
    conj graph_shape (forall x (imp (mem (v x) domain) step_equation))
  in
  Hashtbl.add e.predicates solution (Num (List.length ps + 1)) ;
  record e solution "predicate"
    (ps @ [graph])
    [ ( "equation"
      , foralls
          (ps @ [graph])
          (iff (pred solution (List.map v ps @ [v graph])) solution_body) ) ] ;
  let solution_at g = pred solution (List.map v ps @ [g]) in
  let existence =
    foralls ps
      (exists graph
         (conj
            (solution_at (v graph))
            (forall other_graph
               (imp (solution_at (v other_graph)) (eq (v other_graph) (v graph))))))
  in
  let arity = List.length ps + 1 in
  Hashtbl.add e.functions name (Num arity) ;
  Hashtbl.add e.functions history_name (Num arity) ;
  let value = app name (List.map v ps @ [v x])
  and history = app history_name (List.map v ps @ [v x])
  and previous = app name (List.map v ps @ [v y]) in
  let history_member = fresh "historyMember" !forbidden in
  let history_membership =
    foralls
      (ps @ [x; history_member])
      (iff
         (mem (v history_member) history)
         (exists y
            (conj
               (mem (v y) domain)
               (conj
                  (at_relation (v y) (v x))
                  (eq (v history_member) (pair (v y) previous))))))
  in
  let value_property =
    foralls
      (ps @ [x])
      (imp
         (mem (v x) domain)
         (exists graph
            (conj (solution_at (v graph)) (mem (pair (v x) value) (v graph)))))
  in
  let equation_property =
    foralls
      (ps @ [x])
      (imp
         (mem (v x) domain)
         (exists graph
            (exists h
               (conj
                  (solution_at (v graph))
                  (conj
                     (history_formula (v graph) (v x) (v h))
                     (eq value instantiated_step))))))
  in
  let direct =
    foralls
      (ps @ [x])
      (imp (mem (v x) domain) (eq value (subst_many step [(x, v x); (h, history)])))
  in
  let outside =
    foralls (ps @ [x]) (imp (neg (mem (v x) domain)) (eq value (app "empty" [])))
  in
  record e name "well-founded-set-recursive"
    (ps @ [x])
    [ ("wellFounded", expected_wf)
    ; ("solution.existsUnique", existence)
    ; ("history.membership", history_membership)
    ; ("value", value_property)
    ; ("equation", equation_property)
    ; ("equation.direct", direct)
    ; ("outside", outside) ]

let define_unique e o =
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and value = str (get o "value")
  and relation = get o "relation" in
  fresh_name e name ;
  parameters ps ;
  require (value <> "" && not (List.mem value ps)) "bad unique-description variable" ;
  check_formula e relation ;
  within (free_formula relation) (ps @ [value]) ;
  let other =
    fresh (value ^ "_other")
      (Names.union (names (ps @ [value])) (free_formula relation))
  in
  let expected =
    foralls ps
      (exists value
         (conj relation
            (forall other
               (imp (subst_formula relation value (v other)) (eq (v other) (v value))))))
  in
  Ast_proof.expect e (get o "existsUnique") expected ;
  Hashtbl.add e.functions name (Num (List.length ps)) ;
  let characterization =
    foralls ps (subst_formula relation value (app name (List.map v ps)))
  in
  record e name "unique-choice" ps
    [("existsUnique", expected); ("characterization", characterization)]

let reify_unary e o =
  enabled e "replacement" ;
  let name = str (get o "name")
  and operation = str (get o "operation")
  and domain = get o "domain"
  and codomain = get o "codomain"
  and x = str (get o "variable") in
  fresh_name e name ;
  require (x <> "" && find e.functions operation = Num 1) "bad unary operation" ;
  check_term e domain ;
  check_term e codomain ;
  within (free_term domain) [] ;
  within (free_term codomain) [] ;
  let call = app operation [v x] in
  let in_domain = pred "in" [v x; domain] in
  Ast_proof.expect e (get o "closure")
    (forall x (imp in_domain (pred "in" [call; codomain]))) ;
  Hashtbl.add e.functions name (Num 0) ;
  let graph = app name [] and p = if x = "p" then "pair_" else "p" in
  let membership =
    forall p
      (iff
         (pred "in" [v p; graph])
         (exists x (conj in_domain (eq (v p) (app "orderedPair" [v x; call])))))
  in
  record e name "replacement" []
    [ ("membership", membership)
    ; ("functionOn", pred "functionOn" [graph; domain; codomain])
    ; ("application", forall x (imp in_domain (eq (app "apply" [graph; v x]) call))) ]

let define_well_founded e o =
  let name = str (get o "name")
  and ps = list_strings (get o "parameters")
  and datatype = str (get o "coverageDatatype")
  and pos = num (get o "coverageParameter") in
  let equations = arr (get o "equations")
  and relation = get o "relation"
  and domain = get o "domain"
  and measure = get o "measure" in
  fresh_name e name ;
  parameters ps ;
  List.iter (check_term e) [relation; domain; measure] ;
  within (free_term relation) [] ;
  within (free_term domain) [] ;
  within (free_term measure) ps ;
  let ctors = arr (get (find e.datatypes datatype) "constructors") in
  require
    (pos >= 0 && pos < List.length ps && List.length equations = List.length ctors)
    "bad well-founded coverage" ;
  let wf = pred "wellFoundedOn" [relation; domain]
  and md = foralls ps (pred "in" [measure; domain]) in
  Ast_proof.expect e (get o "wellFounded") wf ;
  Ast_proof.expect e (get o "measureInDomain") md ;
  let seen = ref [] and obligations = ref [] in
  let rec calls t =
    match tag t with
    | "var" | "nat" -> check_term e t ; []
    | "app" ->
        let fn = str (get t "fn") and args = arr (get t "args") in
        if fn = name then require (List.length args = List.length ps) "recursive arity"
        else
          require
            (find e.functions fn = Num (List.length args))
            "recursive-body function" ;
        (if fn = name then [t] else []) @ List.concat_map calls args
    | _ -> fail "bad recursive clause"
  in
  let properties =
    List.mapi
      (fun i q ->
        let patterns = arr (get q "patterns") and body = get q "body" in
        require (List.length patterns = List.length ps) "pattern arity" ;
        List.iteri
          (fun j p ->
            if j <> pos then
              require (tag p = "bind") "non-coverage constructor pattern" )
          patterns ;
        let root = Logic.nth patterns pos in
        require (tag root = "ctor") "coverage constructor required" ;
        let n = str (get root "name") in
        let ctor =
          try List.find (fun c -> str (get c "name") = n) ctors
          with Not_found -> fail "bad coverage constructor"
        in
        require
          ( List.length (arr (get root "args")) = num (get ctor "arity")
          && not (List.mem n !seen) )
          "duplicate constructor equation" ;
        seen := n :: !seen ;
        List.iter (check_pattern e) patterns ;
        let bindings = List.concat_map pattern_bindings patterns in
        parameters bindings ;
        within (free_term body) bindings ;
        let current = List.map pattern_term patterns in
        let current_measure = subst_many measure (List.combine ps current) in
        List.iter
          (fun call ->
            let next_measure =
              subst_many measure (List.combine ps (arr (get call "args")))
            in
            obligations :=
              !obligations
              @ [ foralls bindings
                    (pred "relates" [relation; next_measure; current_measure]) ] )
          (calls body) ;
        ("equation." ^ string_of_int i, foralls bindings (eq (app name current) body))
        )
      equations
  in
  let decreases = arr (get o "decreases") in
  require (List.length decreases = List.length !obligations) "decrease proof count" ;
  List.iter2 (Ast_proof.expect e) decreases !obligations ;
  Hashtbl.add e.functions name (Num (List.length ps)) ;
  Hashtbl.add e.recursive name
    (Obj
       [ ("name", Str name)
       ; ("parameters", strings ps)
       ; ("datatype", Str datatype)
       ; ("decreasingParameter", Num pos)
       ; ("equations", Arr equations)
       ; ("admission", Str "well-founded")
       ; ( "termination"
         , Obj [("relation", relation); ("domain", domain); ("measure", measure)] ) ]) ;
  record e name "well-founded-recursive" ps
    ( properties
    @ [("termination.wellFounded", wf); ("termination.measure", md)]
    @ List.mapi
        (fun i f -> ("termination.decrease." ^ string_of_int i, f))
        !obligations )

let replay e event =
  let operation = str (get event "operation") and p = get event "payload" in
  ignore (obj p) ;
  let s k = str (get p k) in
  let ps () = list_strings (get p "parameters") in
  match operation with
  | "declareFunction" -> declare e e.functions (s "name") (num (get p "arity"))
  | "declarePredicate" -> declare e e.predicates (s "name") (num (get p "arity"))
  | "defineFunction" -> define_function e (s "name") (ps ()) (get p "body")
  | "definePredicate" -> define_predicate e (s "name") (ps ()) (get p "body")
  | "defineSubset" -> define_subset e p
  | "declareDatatype" -> declare_datatype e (get p "spec")
  | "registerNaturalDatatype" -> register_naturals e
  | "defineStructuralFunction" -> define_structural e (get p "options")
  | "defineReplacement" -> define_replacement e (get p "options")
  | "defineMembershipRecursiveFunction" -> define_membership e (get p "options")
  | "defineWellFoundedSetFunction" -> define_well_founded_set e (get p "options")
  | "defineTransfiniteFunction" -> define_transfinite e (get p "options")
  | "defineWellFoundedFunction" -> define_well_founded e (get p "options")
  | "reifyUnaryOperation" -> reify_unary e (get p "options")
  | "defineUniqueFunction" -> define_unique e (get p "options")
  | "addTheorem" ->
      let name = s "name" and statement = get p "statement" in
      require
        (name <> "" && not (Hashtbl.mem e.axioms name || Hashtbl.mem e.theorems name))
        "duplicate theorem" ;
      closed e statement ;
      Ast_proof.expect e (get p "proof") statement ;
      Hashtbl.add e.theorems name statement
  | _ -> fail ("unsupported G17C admission operation " ^ operation)
