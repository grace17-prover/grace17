(* De Bruijn logic: terms, formulas, substitution, and canonical comparison.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support

let at a i = if i < 0 || i >= Array.length a then fail "invalid index" else a.(i)

let nth a i = try List.nth a i with _ -> fail "missing data"

let unique xs =
  let h = Hashtbl.create 64 in
  List.iter
    (fun x ->
      require (not (Hashtbl.mem h x)) "duplicate entry" ;
      Hashtbl.add h x () )
    xs

let natural s =
  String.length s > 0
  && (s = "0" || s.[0] <> '0')
  && String.for_all (fun c -> c >= '0' && c <= '9') s

type term = V of string | B of int | N of Z.t | App of string * term list

type formula =
  | False
  | Eq of term * term
  | Pred of string * term list
  | Imp of formula * formula
  | All of formula
  | And of formula * formula
  | Or of formula * formula
  | Iff of formula * formula
  | Ex of formula

let app name args =
  match (name, args) with
  | "zero", [] -> N Z.zero
  | "succ", [N n] -> N (Z.succ n)
  | _ -> App (name, args)

let rec map_term f depth = function
  | App (n, ts) -> app n (List.map (map_term f depth) ts)
  | t -> f depth t

let rec map_formula f depth = function
  | False -> False
  | Eq (a, b) -> Eq (map_term f depth a, map_term f depth b)
  | Pred (n, ts) -> Pred (n, List.map (map_term f depth) ts)
  | Imp (a, b) -> Imp (map_formula f depth a, map_formula f depth b)
  | And (a, b) -> And (map_formula f depth a, map_formula f depth b)
  | Or (a, b) -> Or (map_formula f depth a, map_formula f depth b)
  | Iff (a, b) -> Iff (map_formula f depth a, map_formula f depth b)
  | All a -> All (map_formula f (depth + 1) a)
  | Ex a -> Ex (map_formula f (depth + 1) a)

let abstract name f =
  map_formula (fun depth t -> match t with V n when n = name -> B depth | _ -> t) 0 f

let shift n t = map_term (fun _ t -> match t with B i -> B (i + n) | _ -> t) 0 t

let subst name term f =
  map_formula
    (fun d t -> match t with V n when n = name -> shift d term | _ -> t)
    0 f

let instantiate term f =
  map_formula
    (fun d t ->
      match t with
      | B i when i = d -> shift d term
      | B i when i > d -> B (i - 1)
      | _ -> t )
    0 f

let rec free_t n = function
  | V x -> x = n
  | App (_, ts) -> List.exists (free_t n) ts
  | _ -> false

let free n f =
  let found = ref false in
  ignore
    (map_formula
       (fun _ t ->
         if free_t n t then found := true ;
         t )
       0 f) ;
  !found

let scope_term depth t =
  ignore
    (map_term
       (fun d t ->
         (match t with B i -> require (i < d) "unbound de Bruijn index" | _ -> ()) ;
         t )
       depth t)

let scope f = ignore (map_formula (fun d t -> scope_term d t ; t) 0 f)

let rec term_json binders j =
  match str (get j "tag") with
  | "var" ->
      let n = str (get j "name") in
      let rec find i = function
        | [] -> V n
        | x :: xs -> if x = n then B i else find (i + 1) xs
      in
      find 0 binders
  | "nat" ->
      let n = str (get j "value") in
      require (natural n) "invalid natural" ;
      N (Z.of_string n)
  | "app" -> app (str (get j "fn")) (List.map (term_json binders) (arr (get j "args")))
  | _ -> fail "invalid environment term"

let rec formula_json binders j =
  let g k = formula_json binders (get j k) and t k = term_json binders (get j k) in
  match str (get j "tag") with
  | "bottom" -> False
  | "eq" -> Eq (t "left", t "right")
  | "pred" ->
      Pred (str (get j "pred"), List.map (term_json binders) (arr (get j "args")))
  | "imp" -> Imp (g "left", g "right")
  | "and" -> And (g "left", g "right")
  | "or" -> Or (g "left", g "right")
  | "iff" -> Iff (g "left", g "right")
  | "forall" -> All (formula_json (str (get j "variable") :: binders) (get j "body"))
  | "exists" -> Ex (formula_json (str (get j "variable") :: binders) (get j "body"))
  | _ -> fail "invalid environment formula"
