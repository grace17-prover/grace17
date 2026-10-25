(* G17M decoding, every inference rule, and theorem boundaries.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Logic

type program =
  { environment: string
  ; symbols: string array
  ; terms: int list array
  ; formulas: int list array
  ; contexts: int list array
  ; code: int list array
  ; root: int
  ; boundaries: (int * int) list }

let decode path =
  let raw = read_file path in
  let n = String.length raw in
  require (n >= 38) "truncated G17M" ;
  let payload = String.sub raw 0 (n - 32) in
  let hex s =
    String.concat ""
      (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))
  in
  require
    (Sha256.digest payload = hex (String.sub raw (n - 32) 32))
    "certificate digest mismatch" ;
  let pos = ref 0 in
  let byte () =
    require (!pos < String.length payload) "truncated certificate" ;
    let b = Char.code payload.[!pos] in
    incr pos ; b
  in
  let uint () =
    let rec loop i v =
      let b = byte () in
      require (i < 5 && (i <> 4 || b <= 15)) "uint overflow" ;
      let v = v lor ((b land 127) lsl (7 * i)) in
      if b < 128 then (
        require (i = 0 || b <> 0) "noncanonical uint" ;
        v )
      else loop (i + 1) v
    in
    loop 0 0
  in
  let count max =
    let n = uint () in
    require (n <= max) "count limit" ;
    n
  in
  let bytes n =
    require (!pos + n <= String.length payload) "truncated bytes" ;
    let s = String.sub payload !pos n in
    pos := !pos + n ;
    s
  in
  require (bytes 4 = "G17M" && byte () = 4) "unsupported G17M version" ;
  let flags = byte () in
  require (flags <= 1) "bad flags" ;
  let environment = hex (bytes 32) in
  let symbols =
    Array.init (count 10000000) (fun _ ->
        let s = bytes (count 1000000) in
        require (s <> "") "empty symbol" ;
        ignore (utf8 s) ;
        s )
  in
  unique (Array.to_list symbols) ;
  let vectors () =
    Array.init (count 10000000) (fun _ -> List.init (count 1000000) (fun _ -> uint ()))
  in
  let terms = vectors () in
  let formulas = vectors () in
  let contexts = vectors () in
  let code = vectors () in
  let root = uint () in
  let boundaries =
    List.init (count 10000000) (fun _ ->
        let a = uint () in
        let b = uint () in
        (a, b) )
  in
  require (flags = 1 = (boundaries <> [])) "boundary flag mismatch" ;
  require (!pos = String.length payload) "trailing certificate bytes" ;
  {environment; symbols; terms; formulas; contexts; code; root; boundaries}

let lookup pairs key =
  match List.assoc_opt key pairs with
  | Some x -> x
  | None -> fail ("unknown environment name " ^ key)

let verify_current ?statements p env =
  let valid_word n = require (n >= 0 && n <= 0xffffffff) "invalid machine word" in
  Array.iter
    (fun s ->
      require (s <> "") "empty symbol" ;
      ignore (utf8 s) )
    p.symbols ;
  unique (Array.to_list p.symbols) ;
  List.iter
    (fun table ->
      require (Array.length table <= 10000000) "arena limit" ;
      Array.iter
        (fun row ->
          require (List.length row <= 1000000) "vector limit" ;
          List.iter valid_word row )
        table )
    [p.terms; p.formulas; p.contexts; p.code] ;
  valid_word p.root ;
  List.iter (fun (a, b) -> valid_word a ; valid_word b) p.boundaries ;
  let functions = pairs (get env "functions")
  and predicates = pairs (get env "predicates") in
  let arity table name n =
    require (num (lookup table name) = n) ("signature mismatch " ^ name)
  in
  let symbol i = at p.symbols i in
  unique_vectors (Array.to_list p.terms) ;
  unique_vectors (Array.to_list p.formulas) ;
  unique_vectors (Array.to_list p.contexts) ;
  let terms = Array.make (Array.length p.terms) (N Z.zero) in
  Array.iteri
    (fun i node ->
      let child k =
        require (k < i) "forward term" ;
        at terms k
      in
      terms.(i)
      <- ( match node with
         | [0; s] -> V (symbol s)
         | [1; k] -> B k
         | [3; s] ->
             let s = symbol s in
             require (natural s) "bad natural" ;
             N (Z.of_string s)
         | 2 :: s :: args ->
             let name = symbol s in
             arity functions name (List.length args) ;
             app name (List.map child args)
         | _ -> fail "bad term node" ) )
    p.terms ;
  let t i = at terms i in
  let formulas = Array.make (Array.length p.formulas) False in
  Array.iteri
    (fun i node ->
      let c k =
        require (k < i) "forward formula" ;
        at formulas k
      in
      formulas.(i)
      <- ( match node with
         | [0] -> False
         | [1; a; b] -> Eq (t a, t b)
         | 2 :: s :: args ->
             let name = symbol s in
             arity predicates name (List.length args) ;
             Pred (name, List.map t args)
         | [3; a; b] -> Imp (c a, c b)
         | [4; a] -> All (c a)
         | [5; a; b] -> And (c a, c b)
         | [6; a; b] -> Or (c a, c b)
         | [7; a; b] -> Iff (c a, c b)
         | [8; a] -> Ex (c a)
         | _ -> fail "bad formula node" ) )
    p.formulas ;
  let f i = at formulas i in
  let contexts =
    Array.map
      (fun xs ->
        List.map
          (fun i ->
            let x = f i in
            scope x ; x )
          xs )
      p.contexts
  in
  let instructions =
    Array.mapi
      (fun pc ins ->
        match ins with
        | op :: claim :: ctx :: n :: rest ->
            require (op <= 29 && n <= List.length rest) "invalid instruction" ;
            scope (f claim) ;
            ignore (at contexts ctx) ;
            let pre =
              Array.init n (fun i ->
                  let q = nth rest i in
                  require (q < pc) "forward premise" ;
                  q )
            in
            let data = Array.of_list (List.filteri (fun i _ -> i >= n) rest) in
            (op, claim, ctx, pre, data)
        | _ -> fail "malformed instruction" )
      p.code
  in
  let closed root =
    let _, _, c, _, _ = at instructions root in
    require
      (at contexts c = [])
      "proof roots and theorem boundaries must have empty contexts"
  in
  closed p.root ;
  unique (List.map fst p.boundaries) ;
  List.iter
    (fun (n, r) ->
      ignore (symbol n) ;
      closed r )
    p.boundaries ;
  let boundaries = List.map (fun (n, r) -> (symbol n, r)) p.boundaries in
  let results = Array.make (Array.length instructions) False in
  let ax = pairs (get env "axioms")
  and th = pairs (get env "theorems")
  and defs = pairs (get env "definitions")
  and datatypes = pairs (get env "datatypes") in
  let imported j = formula_json [] j in
  Array.iteri
    (fun pc (op, claim, ctx, pre, data) ->
      let goal = f claim and context = at contexts ctx in
      let d i = at data i in
      let df i =
        let x = f (d i) in
        scope x ; x
      in
      let dt i =
        let x = t (d i) in
        scope_term 0 x ; x
      in
      let ds i = symbol (d i) in
      let r i = at results (at pre i) in
      let count n = require (Array.length pre = n) "premise count" in
      let words n = require (Array.length data = n) "data length" in
      let branch i expected =
        let _, _, c, _, _ = at instructions (at pre i) in
        require (context_equal (at contexts c) expected) "branch context mismatch"
      in
      let same () = Array.iteri (fun i _ -> branch i context) pre in
      let unary () = count 1 ; same () in
      let binary () = count 2 ; same () in
      let eq = function Eq (a, b) -> (a, b) | _ -> fail "expected equality" in
      let imp = function Imp (a, b) -> (a, b) | _ -> fail "expected implication" in
      let iff = function Iff (a, b) -> (a, b) | _ -> fail "expected equivalence" in
      let derived =
        match op with
        | 0 ->
            count 0 ;
            words 1 ;
            let a = df 0 in
            require (List.exists (formula_equal a) context) "inactive assumption" ;
            a
        | 1 | 2 | 3 -> (
            count 0 ;
            words (if op = 3 then 2 else 1) ;
            let name = ds 0 in
            if op = 1 then imported (lookup ax name)
            else if op = 3 then
              imported (lookup (pairs (get (lookup defs name) "properties")) (ds 1))
            else
              match List.assoc_opt name boundaries with
              | Some root ->
                  require (root < pc) "unproved linked theorem" ;
                  results.(root)
              | None -> imported (lookup th name) )
        | 4 ->
            count 0 ;
            words 1 ;
            let t = dt 0 in
            Eq (t, t)
        | 5 ->
            unary () ;
            words 0 ;
            let a, b = eq (r 0) in
            Eq (b, a)
        | 6 ->
            binary () ;
            words 0 ;
            let a, b = eq (r 0) and c, d = eq (r 1) in
            require (term_equal b c) "transitivity midpoint" ;
            Eq (a, d)
        | 7 ->
            same () ;
            words 1 ;
            arity functions (ds 0) (Array.length pre) ;
            let es = Array.to_list (Array.mapi (fun i _ -> eq (r i)) pre) in
            Eq (app (ds 0) (List.map fst es), app (ds 0) (List.map snd es))
        | 8 ->
            count 1 ;
            words 1 ;
            let a = df 0 in
            branch 0 (context @ [a]) ;
            Imp (a, r 0)
        | 9 ->
            binary () ;
            words 0 ;
            let a, b = imp (r 0) in
            require (formula_equal a (r 1)) "implication argument" ;
            b
        | 10 ->
            unary () ;
            words 1 ;
            let name = ds 0 in
            require (not (List.exists (free name) context)) "generalization freshness" ;
            All (abstract name (r 0))
        | 11 -> (
            unary () ;
            words 1 ;
            match r 0 with
            | All a -> instantiate (dt 0) a
            | _ -> fail "expected universal" )
        | 13 ->
            binary () ;
            words 3 ;
            require (d 2 <= 1) "equality direction" ;
            let a, b = eq (r 0) in
            let a, b = if d 2 = 0 then (a, b) else (b, a) in
            require (formula_equal (r 1) (subst (ds 0) a (df 1))) "equality evidence" ;
            subst (ds 0) b (df 1)
        | 14 ->
            binary () ;
            words 0 ;
            And (r 0, r 1)
        | 15 | 16 -> (
            unary () ;
            words 0 ;
            match r 0 with
            | And (a, b) -> if op = 15 then a else b
            | _ -> fail "expected conjunction" )
        | 17 | 18 ->
            unary () ;
            words 1 ;
            if op = 17 then Or (r 0, df 0) else Or (df 0, r 0)
        | 19 -> (
            count 3 ;
            words 0 ;
            branch 0 context ;
            match r 0 with
            | Or (a, b) ->
                branch 1 (context @ [a]) ;
                branch 2 (context @ [b]) ;
                require (formula_equal (r 1) (r 2)) "disjunction branches" ;
                r 1
            | _ -> fail "expected disjunction" )
        | 20 ->
            binary () ;
            words 0 ;
            let a, b = imp (r 0) and c, d = imp (r 1) in
            require (formula_equal a d && formula_equal b c) "equivalence directions" ;
            Iff (a, b)
        | 21 | 22 ->
            unary () ;
            words 0 ;
            let a, b = iff (r 0) in
            if op = 21 then Imp (a, b) else Imp (b, a)
        | 23 ->
            unary () ;
            words 3 ;
            let body = df 1 in
            require (formula_equal (r 0) (subst (ds 0) (dt 2) body)) "existential instance" ;
            Ex (abstract (ds 0) body)
        | 24 -> (
            count 2 ;
            words 1 ;
            branch 0 context ;
            let name = ds 0 in
            require
              (not (List.exists (free name) (r 0 :: context)))
              "witness freshness" ;
            match r 0 with
            | Ex body ->
                branch 1 (context @ [instantiate (V name) body]) ;
                require (not (free name (r 1))) "witness escapes" ;
                r 1
            | _ -> fail "expected existential" )
        | 25 ->
            unary () ;
            words 1 ;
            require (r 0 = False) "false elimination" ;
            df 0
        | 26 ->
            unary () ;
            words 1 ;
            let a = df 0 in
            require (formula_equal (r 0) (Imp (Imp (a, False), False))) "double negation" ;
            a
        | 27 ->
            binary () ;
            words 5 ;
            let rel = dt 0
            and domain = dt 1
            and x = ds 2
            and y = ds 3
            and motive = df 4 in
            require
              ( x <> y
              && not
                   ( free_t x rel || free_t y rel || free_t x domain || free_t y domain
                   || free y motive
                   || List.exists (fun a -> free x a || free y a) context ) )
              "well-founded freshness" ;
            require
              (formula_equal (r 0) (Pred ("wellFoundedOn", [rel; domain])))
              "well-founded certificate" ;
            let member = Pred ("in", [V x; domain]) in
            let ih =
              All
                (abstract y
                   (Imp
                      ( And
                          ( Pred ("in", [V y; domain])
                          , Pred ("relates", [rel; V y; V x]) )
                      , subst x (V y) motive )))
            in
            require
              (formula_equal (r 1) (All (abstract x (Imp (member, Imp (ih, motive))))))
              "well-founded step" ;
            All (abstract x (Imp (member, motive)))
        | 12 ->
            require (Array.length data >= 5) "induction data" ;
            let datatype = lookup datatypes (ds 0) in
            let x = ds 1 and motive = df 2 and np = d 3 in
            require
              (np = List.length (arr (optional datatype "parameters" (Arr []))))
              "datatype parameters" ;
            let params = List.init np (fun i -> dt (4 + i)) in
            let nc = d (4 + np) in
            let ctors = arr (get datatype "constructors") in
            count nc ;
            require (nc = List.length ctors) "constructor count" ;
            require
              (not (List.exists (free_t x) params || List.exists (free x) context))
              "induction freshness" ;
            let cursor = ref (5 + np) and seen = ref [] in
            List.iteri
              (fun i _ ->
                let name = ds !cursor in
                let nf = d (!cursor + 1) in
                cursor := !cursor + 2 ;
                let fields = List.init nf (fun j -> ds (!cursor + j)) in
                cursor := !cursor + nf ;
                unique fields ;
                require (not (List.mem name !seen)) "duplicate constructor" ;
                seen := name :: !seen ;
                let ctor =
                  try List.find (fun c -> str (get c "name") = name) ctors
                  with Not_found -> fail "unknown constructor"
                in
                require (nf = num (get ctor "arity")) "constructor arity" ;
                List.iter
                  (fun n ->
                    require
                      ( n <> x
                      && not
                           ( free n motive
                           || List.exists (free_t n) params
                           || List.exists (free n) context ) )
                      "induction field freshness" )
                  fields ;
                let field_terms = List.map (fun n -> V n) fields in
                let expected = ref context in
                List.iteri
                  (fun j term ->
                    if List.mem (Num j) (arr (get ctor "recursiveFields")) then
                      expected :=
                        !expected
                        @ [ Pred (str (get datatype "predicate"), params @ [term])
                          ; subst x term motive ]
                    else
                      List.iter
                        (fun entry ->
                          if num (get entry "field") = j then
                            expected :=
                              !expected
                              @ [ Pred
                                    ( "in"
                                    , [term; nth params (num (get entry "parameter"))]
                                    ) ] )
                        (arr (optional ctor "parameterFields" (Arr []))) )
                  field_terms ;
                branch i !expected ;
                require (formula_equal (r i) (subst x (app name field_terms) motive)) "induction case"
                )
              ctors ;
            require (!cursor = Array.length data) "extra induction data" ;
            All
              (abstract x
                 (Imp (Pred (str (get datatype "predicate"), params @ [V x]), motive)))
        | 28 ->
            count 0 ;
            require (Array.length data > 0) "computation data" ;
            words (1 + d 0) ;
            Compute.check env goal (List.init (d 0) (fun i -> ds (i + 1))) ;
            goal
        | 29 -> count 0 ; words 0 ; Compute.rational env goal ; goal
        | _ -> fail "unknown opcode"
      in
      require (derived = goal) (Printf.sprintf "wrong conclusion at instruction %d" pc) ;
      results.(pc) <- derived )
    instructions ;
  let expected = match statements with Some xs -> xs | None -> th in
  List.iter
    (fun (n, root) ->
      require
        (results.(root) = imported (lookup expected n))
        ("theorem boundary mismatch " ^ n) )
    boundaries ;
  (Array.length instructions, List.length boundaries)

let verify p document =
  require
    ( get document "format" = Str "grace17.environment"
    && get document "version" = Num 1 )
    "unsupported environment" ;
  let env = get document "kernel" in
  let digest = Sha256.digest (canonical env) in
  require
    (digest = str (get document "digest") && digest = p.environment)
    "environment digest mismatch" ;
  verify_current p env

let from_json j =
  require (get j "version" = Num 4) "embedded G17M version" ;
  let vectors k =
    Array.of_list (List.map (fun row -> List.map num (arr row)) (arr (get j k)))
  in
  let boundaries =
    List.map
      (function Arr [Num a; Num b] -> (a, b) | _ -> fail "bad theorem boundary")
      (arr (get j "theorems"))
  in
  { environment= str (get j "environment")
  ; symbols= Array.of_list (List.map str (arr (get j "symbols")))
  ; terms= vectors "terms"
  ; formulas= vectors "formulas"
  ; contexts= vectors "contexts"
  ; code= vectors "code"
  ; root= num (get j "root")
  ; boundaries }
