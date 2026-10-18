(* Declaration proof DAGs, including both induction rules.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Logic
module E = Environment

let decode wrapper =
  require (List.map fst (obj wrapper) = ["$grace17ProofDag"]) "bad proof wrapper" ;
  let dag = get wrapper "$grace17ProofDag" in
  let body =
    Obj
      [ ("version", get dag "version")
      ; ("nodes", get dag "nodes")
      ; ("root", get dag "root") ]
  in
  require
    ( get dag "version" = Num 1
    && Sha256.digest (canonical body) = str (get dag "digest") )
    "bad proof DAG digest" ;
  let nodes = Array.of_list (arr (get dag "nodes")) in
  let decoded = Array.make (Array.length nodes) Null in
  let rec value pc = function
    | Obj [("$proof", Num i)] ->
        require (i >= 0 && i < pc) "forward proof reference" ;
        decoded.(i)
    | Obj xs -> Obj (List.map (fun (k, v) -> (k, value pc v)) xs)
    | Arr xs -> Arr (List.map (value pc) xs)
    | x -> x
  in
  Array.iteri
    (fun pc n ->
      require (List.map fst (obj n) = ["payload"]) "bad DAG node" ;
      let p = value pc (get n "payload") in
      ignore (str (get p "rule")) ;
      decoded.(pc) <- p )
    nodes ;
  at decoded (num (get dag "root"))

module Cache = Hashtbl.Make (struct
  type t = json * formula list

  let equal (a, c) (b, d) = a == b && c = d

  let hash = Hashtbl.hash
end)

let check e wrapper =
  let proof = decode wrapper and cache = Cache.create 128 in
  let env = lazy (E.snapshot e) in
  let rec check assumptions proof =
    match Cache.find_opt cache (proof, assumptions) with
    | Some f -> f
    | None ->
        let g k = get proof k and s k = str (get proof k) in
        let f k =
          let x = g k in
          E.check_formula e x ; formula_json [] x
        in
        let t k =
          let x = g k in
          E.check_term e x ; term_json [] x
        in
        let p k = check assumptions (g k) in
        let eq = function
          | Eq (a, b) -> (a, b)
          | _ -> fail "expected proof equality"
        in
        let imp = function Imp (a, b) -> (a, b) | _ -> fail "expected implication" in
        let result =
          match s "rule" with
          | "assumption" ->
              let a = f "formula" in
              require (List.mem a assumptions) "inactive assumption" ;
              a
          | "axiom" -> formula_json [] (E.find e.axioms (s "name"))
          | "theorem" -> formula_json [] (E.find e.theorems (s "name"))
          | "definition" ->
              formula_json []
                (E.property e (s "name")
                   (str (optional proof "property" (Str "equation"))))
          | "refl" ->
              let x = t "term" in
              Eq (x, x)
          | "compute" ->
              let a = Eq (t "left", t "right") in
              Compute.check (Lazy.force env) a (List.map str (arr (g "definitions"))) ;
              a
          | "rationalClassCompute" ->
              let a = Eq (t "left", t "right") in
              Compute.rational (Lazy.force env) a ;
              a
          | "symm" ->
              let a, b = eq (p "proof") in
              Eq (b, a)
          | "trans" ->
              let a, b = eq (p "left") and c, d = eq (p "right") in
              require (b = c) "bad transitivity" ;
              Eq (a, d)
          | "congr" ->
              let es =
                List.map (fun q -> eq (check assumptions q)) (arr (g "proofs"))
              in
              require
                (E.find e.functions (s "fn") = Num (List.length es))
                "congruence arity" ;
              Eq (app (s "fn") (List.map fst es), app (s "fn") (List.map snd es))
          | "impIntro" ->
              let a = f "assumption" in
              Imp (a, check (assumptions @ [a]) (g "body"))
          | "impElim" ->
              let a, b = imp (p "implication") in
              require (a = p "argument") "implication mismatch" ;
              b
          | "forallIntro" ->
              let n = s "variable" in
              require
                (n <> "" && not (List.exists (free n) assumptions))
                "generalization freshness" ;
              All (abstract n (p "body"))
          | "forallElim" -> (
            match p "universal" with
            | All a -> instantiate (t "term") a
            | _ -> fail "expected universal" )
          | "eqElim" ->
              let a, b = eq (p "equality") in
              let reverse = optional proof "reverse" (Bool false) in
              require (reverse = Bool true || reverse = Bool false) "bad direction" ;
              let a, b = if reverse = Bool true then (b, a) else (a, b) in
              let motive = f "motive" in
              require
                (p "evidence" = subst (s "variable") a motive)
                "equality evidence" ;
              subst (s "variable") b motive
          | "andIntro" -> And (p "left", p "right")
          | "andElimLeft" | "andElimRight" -> (
            match p "conjunction" with
            | And (a, b) -> if s "rule" = "andElimLeft" then a else b
            | _ -> fail "expected conjunction" )
          | "orIntroLeft" -> Or (p "proof", f "right")
          | "orIntroRight" -> Or (f "left", p "proof")
          | "orElim" -> (
            match p "disjunction" with
            | Or (a, b) ->
                let l = check (assumptions @ [a]) (g "left")
                and r = check (assumptions @ [b]) (g "right") in
                require (l = r) "or branches" ;
                l
            | _ -> fail "expected disjunction" )
          | "iffIntro" ->
              let a, b = imp (p "forward") and c, d = imp (p "backward") in
              require (a = d && b = c) "iff directions" ;
              Iff (a, b)
          | "iffElimLeft" | "iffElimRight" -> (
            match p "equivalence" with
            | Iff (a, b) -> if s "rule" = "iffElimLeft" then Imp (a, b) else Imp (b, a)
            | _ -> fail "expected equivalence" )
          | "existsIntro" ->
              let body = f "body" in
              require
                (p "evidence" = subst (s "variable") (t "witness") body)
                "bad existential instance" ;
              Ex (abstract (s "variable") body)
          | "existsElim" -> (
              let existential = p "existential" and n = s "witness" in
              require
                (n <> "" && not (List.exists (free n) (existential :: assumptions)))
                "witness freshness" ;
              match existential with
              | Ex a ->
                  let r = check (assumptions @ [instantiate (V n) a]) (g "body") in
                  require (not (free n r)) "escaping witness" ;
                  r
              | _ -> fail "expected existential" )
          | "falseElim" ->
              require (p "absurdity" = False) "expected false" ;
              f "conclusion"
          | "dne" ->
              let a = f "proposition" in
              require (p "proof" = Imp (Imp (a, False), False)) "bad double negation" ;
              a
          | "wellFoundedInduction" ->
              let rel = t "relation"
              and domain = t "domain"
              and x = s "variable"
              and y = s "predecessor"
              and motive = f "motive" in
              require
                ( x <> y
                && not
                     ( free_t x rel || free_t y rel || free_t x domain
                     || free_t y domain || free y motive
                     || List.exists (fun a -> free x a || free y a) assumptions ) )
                "well-founded freshness" ;
              require
                (p "wellFounded" = Pred ("wellFoundedOn", [rel; domain]))
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
                (p "step" = All (abstract x (Imp (member, Imp (ih, motive)))))
                "well-founded step" ;
              All (abstract x (Imp (member, motive)))
          | "induction" ->
              let datatype = E.find e.datatypes (s "datatype")
              and x = s "variable"
              and motive = f "motive" in
              let params =
                List.map
                  (fun t -> E.check_term e t ; term_json [] t)
                  (arr (g "parameters"))
              in
              require
                ( List.length params
                = List.length (arr (optional datatype "parameters" (Arr []))) )
                "induction parameters" ;
              require
                (not (List.exists (free_t x) params || List.exists (free x) assumptions))
                "induction variable freshness" ;
              let ctors = arr (get datatype "constructors")
              and cases = arr (g "cases") in
              require (List.length ctors = List.length cases) "induction cases" ;
              unique (List.map (fun c -> str (get c "constructor")) cases) ;
              List.iter
                (fun c ->
                  let n = str (get c "constructor")
                  and fields = List.map str (arr (get c "fields")) in
                  let ctor =
                    try List.find (fun q -> str (get q "name") = n) ctors
                    with Not_found -> fail "unknown constructor"
                  in
                  unique fields ;
                  require
                    (List.length fields = num (get ctor "arity"))
                    "constructor fields" ;
                  List.iter
                    (fun n ->
                      require
                        ( n <> x
                        && not
                             ( free n motive
                             || List.exists (free_t n) params
                             || List.exists (free n) assumptions ) )
                        "field freshness" )
                    fields ;
                  let ts = List.map (fun n -> V n) fields in
                  let context = ref assumptions in
                  List.iteri
                    (fun i t ->
                      if List.mem (Num i) (arr (get ctor "recursiveFields")) then
                        context :=
                          !context
                          @ [ Pred (str (get datatype "predicate"), params @ [t])
                            ; subst x t motive ]
                      else
                        List.iter
                          (fun q ->
                            if num (get q "field") = i then
                              context :=
                                !context
                                @ [ Pred
                                      ("in", [t; nth params (num (get q "parameter"))])
                                  ] )
                          (arr (optional ctor "parameterFields" (Arr []))) )
                    ts ;
                  require
                    (check !context (get c "proof") = subst x (app n ts) motive)
                    "induction branch" )
                cases ;
              All
                (abstract x
                   (Imp (Pred (str (get datatype "predicate"), params @ [V x]), motive)))
          | rule -> fail ("unsupported AST proof rule " ^ rule)
        in
        Cache.add cache (proof, assumptions) result ;
        result
  in
  check [] proof

let expect e proof formula =
  E.check_formula e formula ;
  require
    (check e proof = Logic.formula_json [] formula)
    "admission proof has wrong conclusion"
