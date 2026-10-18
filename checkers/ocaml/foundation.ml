(* Explicit ZF, ZFC, and ZFG foundation construction.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

open Support
open Named
open Environment

let construct profile =
  let e = create profile in
  List.iter
    (fun (n, a) -> declare e e.functions n a)
    [ ("empty", 0)
    ; ("pair", 2)
    ; ("union", 1)
    ; ("powerset", 1)
    ; ("omega", 0)
    ; ("apply", 2)
    ; ("epsilon0", 0) ] ;
  declare e e.predicates "in" 2 ;
  let x = v "x" and y = v "y" and z = v "z" in
  let member a b = pred "in" [a; b] in
  let empty = app "empty" [] and omega = app "omega" [] in
  add_axiom e "set.empty" (forall "x" (neg (member x empty))) ;
  add_axiom e "set.pairing"
    (foralls ["x"; "y"; "z"]
       (iff (member z (app "pair" [x; y])) (disj (eq z x) (eq z y)))) ;
  add_axiom e "set.extensionality"
    (foralls ["x"; "y"] (imp (forall "z" (iff (member z x) (member z y))) (eq x y))) ;
  define_predicate e "subset" ["x"; "y"] (forall "z" (imp (member z x) (member z y))) ;
  add_axiom e "set.union"
    (foralls ["A"; "x"]
       (iff
          (member x (app "union" [v "A"]))
          (exists "y" (conj (member y (v "A")) (member x y))))) ;
  add_axiom e "set.powerset"
    (foralls ["x"; "y"]
       (iff
          (member x (app "powerset" [y]))
          (forall "z" (imp (member z x) (member z y))))) ;
  define_function e "singleton" ["x"] (app "pair" [x; x]) ;
  define_function e "union2" ["x"; "y"] (app "union" [app "pair" [x; y]]) ;
  define_function e "orderedPair" ["x"; "y"]
    (app "pair" [app "pair" [x; x]; app "pair" [x; y]]) ;
  define_function e "cons" ["x"; "y"] (app "orderedPair" [x; y]) ;
  define_function e "zero" [] empty ;
  let successor = app "union" [app "pair" [v "n"; app "pair" [v "n"; v "n"]]] in
  define_function e "succ" ["n"] successor ;
  define_predicate e "Nat" ["n"] (member (v "n") omega) ;
  define_predicate e "relates" ["r"; "x"; "y"]
    (member (app "orderedPair" [x; y]) (v "r")) ;
  let relates a b = pred "relates" [v "f"; a; b] in
  let function_on =
    conj
      (forall "x"
         (imp
            (member x (v "A"))
            (exists "y"
               (conj
                  (member y (v "B"))
                  (conj (relates x y) (forall "z" (imp (relates x z) (eq z y))))))))
      (forall "p"
         (imp
            (member (v "p") (v "f"))
            (exists "x"
               (exists "y"
                  (conj
                     (member x (v "A"))
                     (conj (member y (v "B")) (eq (v "p") (app "orderedPair" [x; y]))))))))
  in
  define_predicate e "functionOn" ["f"; "A"; "B"] function_on ;
  add_axiom e "function.apply"
    (foralls ["f"; "A"; "B"; "x"; "y"]
       (imp
          (conj
             (pred "functionOn" [v "f"; v "A"; v "B"])
             (conj (member x (v "A")) (relates x y)))
          (eq (app "apply" [v "f"; x]) y))) ;
  let inductive a =
    conj (member empty a) (forall "n" (imp (member (v "n") a) (member successor a)))
  in
  add_axiom e "set.infinity" (inductive omega) ;
  add_axiom e "set.infinity.minimal"
    (forall "A"
       (imp
          (inductive (v "A"))
          (forall "n" (imp (member (v "n") omega) (member (v "n") (v "A")))))) ;
  add_axiom e "set.foundation"
    (forall "x"
       (imp
          (neg (eq x empty))
          (exists "y"
             (conj (member y x) (forall "z" (imp (member z y) (neg (member z x)))))))) ;
  define_predicate e "wellFoundedOn" ["r"; "A"]
    (forall "s"
       (imp
          (conj (pred "subset" [v "s"; v "A"]) (neg (eq (v "s") empty)))
          (exists "m"
             (conj
                (member (v "m") (v "s"))
                (forall "y"
                   (imp (member y (v "s")) (neg (pred "relates" [v "r"; y; v "m"])))))))) ;
  define_predicate e "E0Ordinal" ["x"] (member x (app "epsilon0" [])) ;
  if profile = "ZFC" || profile = "ZFG" then
    add_axiom e "set.choice"
      (forall "A"
         (imp
            (forall "x" (imp (member x (v "A")) (exists "y" (member y x))))
            (exists "f"
               (conj
                  (pred "functionOn" [v "f"; v "A"; app "union" [v "A"]])
                  (forall "x"
                     (imp (member x (v "A")) (member (app "apply" [v "f"; x]) x))))))) ;
  if profile = "ZFG" then (
    declare e e.functions "choose" 1 ;
    add_axiom e "set.globalChoice"
      (forall "A"
         (imp (neg (eq (v "A") empty)) (member (app "choose" [v "A"]) (v "A")))) ) ;
  Admissions.register_naturals e ;
  refresh e ;
  e.foundation <- e.digest ;
  e

let load value =
  if List.mem value ["ZF"; "ZFC"; "ZFG"] then construct value
  else
    let document = parse (read_file value) in
    require
      ( List.sort compare (List.map fst (obj document))
        = ["environment"; "format"; "profile"; "version"]
      && get document "format" = Str "grace17.foundation"
      && get document "version" = Num 1 )
      "expected foundation receipt, not a trusted environment" ;
    let e = construct (str (get document "profile")) in
    require (e.digest = str (get document "environment")) "foundation receipt mismatch" ;
    e
