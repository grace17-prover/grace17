(* Named declaration syntax for deterministic reconstruction of declaration receipts.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

(* Logical equality itself uses Logic's de Bruijn representation. *)
open Support
module Names = Set.Make (String)

let names xs = List.fold_left (fun s x -> Names.add x s) Names.empty xs

let strings xs = Arr (List.map (fun s -> Str s) xs)

let v name = Obj [("tag", Str "var"); ("name", Str name)]

let app fn args = Obj [("tag", Str "app"); ("fn", Str fn); ("args", Arr args)]

let nat n = Obj [("tag", Str "nat"); ("value", Str n)]

let bottom = Obj [("tag", Str "bottom")]

let eq left right = Obj [("tag", Str "eq"); ("left", left); ("right", right)]

let pred name args = Obj [("tag", Str "pred"); ("pred", Str name); ("args", Arr args)]

let binary tag left right = Obj [("tag", Str tag); ("left", left); ("right", right)]

let imp = binary "imp"

let conj = binary "and"

let disj = binary "or"

let iff = binary "iff"

let neg a = imp a bottom

let quantify tag variable body =
  Obj [("tag", Str tag); ("variable", Str variable); ("body", body)]

let forall = quantify "forall"

let exists = quantify "exists"

let foralls xs body = List.fold_right forall xs body

let tag j = str (get j "tag")

let same_term a b = Logic.term_json [] a = Logic.term_json [] b

let same_formula a b = Logic.formula_json [] a = Logic.formula_json [] b

let rec free_term t =
  match tag t with
  | "var" -> Names.singleton (str (get t "name"))
  | "nat" -> Names.empty
  | "app" ->
      List.fold_left
        (fun s t -> Names.union s (free_term t))
        Names.empty
        (arr (get t "args"))
  | _ -> fail "malformed term"

let rec free_formula f =
  match tag f with
  | "bottom" -> Names.empty
  | "eq" -> Names.union (free_term (get f "left")) (free_term (get f "right"))
  | "pred" ->
      List.fold_left
        (fun s t -> Names.union s (free_term t))
        Names.empty
        (arr (get f "args"))
  | "imp" | "and" | "or" | "iff" ->
      Names.union (free_formula (get f "left")) (free_formula (get f "right"))
  | "forall" | "exists" ->
      Names.remove (str (get f "variable")) (free_formula (get f "body"))
  | _ -> fail "malformed formula"

let fresh base forbidden =
  let rec loop i =
    let n = if i = 0 then base else base ^ "_" ^ string_of_int i in
    if Names.mem n forbidden then loop (i + 1) else n
  in
  loop 0

let rec subst_term t variable replacement =
  match tag t with
  | "var" when str (get t "name") = variable -> replacement
  | "app" ->
      app
        (str (get t "fn"))
        (List.map (fun t -> subst_term t variable replacement) (arr (get t "args")))
  | _ -> t

let rec subst_formula f variable replacement =
  match tag f with
  | "bottom" -> f
  | "eq" ->
      eq
        (subst_term (get f "left") variable replacement)
        (subst_term (get f "right") variable replacement)
  | "pred" ->
      pred
        (str (get f "pred"))
        (List.map (fun t -> subst_term t variable replacement) (arr (get f "args")))
  | ("imp" | "and" | "or" | "iff") as k ->
      binary k
        (subst_formula (get f "left") variable replacement)
        (subst_formula (get f "right") variable replacement)
  | ("forall" | "exists") as k ->
      let binder = str (get f "variable") and body = get f "body" in
      if binder = variable then f
      else if
        Names.mem binder (free_term replacement)
        && Names.mem variable (free_formula body)
      then
        let renamed =
          fresh binder
            (Names.add variable
               (Names.union (free_formula body) (free_term replacement)))
        in
        quantify k renamed
          (subst_formula (subst_formula body binder (v renamed)) variable replacement)
      else quantify k binder (subst_formula body variable replacement)
  | _ -> fail "malformed substitution formula"

let subst_many t bindings =
  List.fold_left (fun t (n, v) -> subst_term t n v) t bindings

let rec functions t =
  if tag t = "app" then
    List.fold_left
      (fun s t -> Names.union s (functions t))
      (Names.singleton (str (get t "fn")))
      (arr (get t "args"))
  else Names.empty

let rec symbols f =
  match tag f with
  | "bottom" -> Names.empty
  | "eq" -> Names.union (functions (get f "left")) (functions (get f "right"))
  | "pred" ->
      List.fold_left
        (fun s t -> Names.union s (functions t))
        (Names.singleton (str (get f "pred")))
        (arr (get f "args"))
  | "forall" | "exists" -> symbols (get f "body")
  | _ -> Names.union (symbols (get f "left")) (symbols (get f "right"))

let rec pattern_bindings p =
  match tag p with
  | "bind" -> [str (get p "name")]
  | "ctor" -> List.concat_map pattern_bindings (arr (get p "args"))
  | _ -> fail "bad pattern"

let rec pattern_term p =
  match tag p with
  | "bind" -> v (str (get p "name"))
  | "ctor" -> app (str (get p "name")) (List.map pattern_term (arr (get p "args")))
  | _ -> fail "bad pattern"
