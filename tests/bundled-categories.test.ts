// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled categories: a category is one set C, a `structure` with
// projections printed as C.obj, functors and transformations are bundled too, `F(x)` reads obj(F)(x) or map(F)(x)
// off the local facts, Set-valued functors apply as functions, the unfolding
// of Functor presents hom-typed binders, and the pilot theorems of the
// Category area stay within their line budgets.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createZfKernel, formulaEquals, loadModuleSourceGraph } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module Bundled\nimport Grace.Cumulus.Category\n";

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Bundled.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "Bundled.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

test("a category is one set: ∘ and ⟶ resolve from Category(C) through C.comp, C.mor, C.dom, C.cod", () => {
  const written = load(header + `
theorem unit (C a b f : Set)
  requires category : Category(C)
  requires fHom : f : a ⟶ b
  shows id(C)(b) ∘ f = f
proof
  exact Category.id_left with *
`);
  const spelled = load(header + `
theorem unit (C a b f : Set)
  requires category : Category(C)
  requires fHom : Morphism(C, f, a, b)
  shows comp(C)(id(C)(b), f) = f
proof
  exact Category.id_left with *
`);
  assert.ok(formulaEquals(written.theorems.get("Bundled.unit")!, spelled.theorems.get("Bundled.unit")!));
  assert.ok(formulaEquals(load(header + `
theorem projections (O M d c e m : Set)
  shows obj(Category.mk(O, M, d, c, e, m)) = O ∧ comp(Category.mk(O, M, d, c, e, m)) = m
proof
  category_projections
`).theorems.get("Bundled.projections")!, load(header + `
theorem projections (O M d c e m : Set)
  shows Category.obj(Category.mk(O, M, d, c, e, m)) = O ∧ Category.comp(Category.mk(O, M, d, c, e, m)) = m
proof
  constructor
  . exact Category.mk.obj at O, M, d, c, e, m
  . exact Category.mk.comp at O, M, d, c, e, m
`).theorems.get("Bundled.projections")!));
});

test("F : C ⥤ D and η : F ⟹ G are guards; F applied to an object is obj(F), to a morphism map(F), and the statement prints F applied", () => {
  const source = header + `
section S
variable (η F G C D : Set)
hypothesis functorF : F : C ⥤ D
hypothesis functorG : G : C ⥤ D
hypothesis natural : η : F ⟹ G

theorem square (a b ∈ obj(C)) (f : a ⟶ b)
  shows η(b) ∘ F(f) = G(f) ∘ η(a)
proof
  functor_simp

theorem object (a ∈ obj(C))
  shows F(a) ∈ obj(D)
proof
  exact Functor.object_closed with *
end S
`;
  const result = check(source);
  const square = result.theorems.find(item => item.name === "Bundled.square")!.statement;
  assert.match(square, /∀ \(f : a ⟶ b\), Functor\(F, C, D\) → Functor\(G, C, D\) → NaturalTransformation\(η, F, G\) → η\(b\) ∘ F\(f\) = G\(f\) ∘ η\(a\)$/u);
  const spelled = load(source.replace("shows η(b) ∘ F(f) = G(f) ∘ η(a)", "shows comp(D)(η(b), map(F)(f)) = comp(D)(map(G)(f), η(a))")
    .replace("shows F(a) ∈ obj(D)", "shows obj(F)(a) ∈ obj(D)"));
  assert.ok(formulaEquals(load(source).theorems.get("Bundled.square")!, spelled.theorems.get("Bundled.square")!));
  assert.ok(formulaEquals(load(source).theorems.get("Bundled.object")!, spelled.theorems.get("Bundled.object")!));
});

test("an argument of a functor that the facts place neither among the objects nor the morphisms is an error naming both spellings", () => {
  assert.throws(() => load(header + `
theorem loose (F C D x : Set)
  requires functor : F : C ⥤ D
  shows F(x) = F(x)
proof
  rfl
`), /F is a functor, and x is not known to be an object or a morphism of C.*obj\(F\)\(x\).*map\(F\)\(f\)/u);
});

test("a Set-valued functor applies as a function: F(g ∘ f)(x) = F(g)(F(f)(x)) is one simp, and pointwise equality is Sets.ext", () => {
  check(header + `
section S
variable (F C U : Set)
hypothesis functor : F : C ⥤ Sets(U)

theorem pointwise (a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c) (x : Set)
  requires xIn : x ∈ F(a)
  shows F(g ∘ f)(x) = F(g)(F(f)(x))
proof
  simp [Functor.map_comp, Sets.comp_apply]

theorem value (a b ∈ obj(C)) (f : a ⟶ b) (x : Set)
  requires xIn : x ∈ F(a)
  shows F(f)(x) ∈ F(b)
proof
  have image : F(f) : F(a) ⟶ F(b) := Functor.map_hom with *
  exact Sets.apply_closed with *

theorem extensional (a b ∈ obj(C)) (f g : a ⟶ b)
  requires same : ∀ x ∈ F(a), F(f)(x) = F(g)(x)
  shows F(f) = F(g)
proof
  have sets := Sets.category at U
  have fImage : F(f) : F(a) ⟶ F(b) := Functor.map_hom with *
  have gImage : F(g) : F(a) ⟶ F(b) := Functor.map_hom with *
  exact Sets.ext with fImage, gImage, sets, same
end S
`);
});

test("the unfolding of Functor presents hom-typed binders, so a functoriality proof opens with a typed intros", () => {
  const result = check(header + `
theorem laws (F C D : Set)
  requires functor : F : C ⥤ D
  shows ∀ (a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c), F(g ∘ f) = F(g) ∘ F(f)
proof
  obtain ⟨shape, source, target, objects, morphisms, homs, identities, composites, srcF, tgtF⟩ := functor
  intros a aIn b bIn c cIn f fHom g gHom
  exact composites with a, aIn, b, bIn, c, cIn, f, fHom, g, gHom
`);
  const statement = result.theorems.find(item => item.name === "Bundled.laws")!.statement;
  assert.match(statement, /∀ c ∈ C\.obj, ∀ \(f : a ⟶ b\), ∀ \(g : b ⟶ c\), F\(g ∘ f\) = F\(g\) ∘ F\(f\)$/u);
});

test("a defgraph transformation exposes its components as hom guards and is a transformation by the constructor", () => {
  check(header + `
section S
variable (η θ F G H C D : Set)
hypothesis functorF : F : C ⥤ D
hypothesis functorG : G : C ⥤ D
hypothesis functorH : H : C ⥤ D
hypothesis etaNatural : η : F ⟹ G
hypothesis thetaNatural : θ : G ⟹ H

theorem component (a ∈ obj(C))
  shows verticalComposition(η, θ, F, G, H)(a) : F(a) ⟶ H(a)
proof
  rw verticalComposition.component
  synthesize

theorem composite
  shows verticalComposition(η, θ, F, G, H) : F ⟹ H
proof
  exact verticalComposition.natural with *
end S
`);
});

test("the pilot theorems stay within their line budgets and the Yoneda lemma reads NatTrans(homFunctor(C, U, a), F) ≃ F(a)", () => {
  const lines = (file: string, name: string): number => {
    const source = readFileSync(`lib/Grace/Cumulus/Category/${file}`, "utf8");
    const match = new RegExp(`^(?:theorem|instance) ${name.replace(/\./g, "\\.")}\\b[\\s\\S]*?\\nproof\\n([\\s\\S]*?)\\n\\n`, "mu").exec(source);
    assert.ok(match, `${name} in ${file}`);
    return match![1]!.split("\n").filter(line => line.trim()).length;
  };
  assert.equal(lines("Isomorphism.g17", "InversePair.unique"), 6);
  assert.ok(lines("Functor.g17", "Functor.compose") <= 10);
  assert.ok(lines("Natural.g17", "verticalComposition.natural") <= 10);
  assert.ok(lines("Yoneda.g17", "yonedaTransformation.natural") <= 16);
  assert.ok(lines("Yoneda.g17", "yonedaMap.inverse") <= 10);
  assert.ok(lines("Yoneda.g17", "yonedaInverse.map") <= 14);
  const yoneda = readFileSync("lib/Grace/Cumulus/Category/Yoneda.g17", "utf8");
  assert.match(yoneda, /theorem yoneda \(C U F a : Set\)\n  requires functor : F : C ⥤ Sets\(U\)\n  requires small : mor\(C\) ⊆ U\n  requires aInO : a ∈ obj\(C\)\n  shows NatTrans\(homFunctor\(C, U, a\), F\) ≃ F\(a\)/u);
});
