// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The categorical rewrite set: `simp` and `rw` apply the unit laws,
// associativity, functoriality, and naturality as conditional rewrite rules
// whose hom guards are discharged from the guards in scope, binding the
// objects the left-hand side leaves open, and `category_simp` and
// `functor_simp` name the sets.

import assert from "node:assert/strict";
import test from "node:test";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module CategorySimp\nimport Grace.Cumulus.Category.Natural\n";

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "CategorySimp.g17", source: header + source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 600));
}

test("unit laws and associativity rewrite under hom guards, including on composites", () => {
  check(`
section S
variable (C : Set)
hypothesis category : Category(C)

theorem units (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows (id(C)(c) ∘ g) ∘ (f ∘ id(C)(a)) = g ∘ f
proof
  category_simp

theorem regroup (a b c d : Set) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  shows h ∘ (g ∘ f) = (h ∘ g) ∘ f
proof
  rw Category.assoc
  rfl

theorem both (a b c d : Set) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  shows (id(C)(d) ∘ h) ∘ (g ∘ f) = (h ∘ g) ∘ (f ∘ id(C)(a))
proof
  simp [Category.id_left, Category.id_right, Category.assoc]

theorem idempotent (a : Set)
  requires aInO : a ∈ obj(C)
  shows id(C)(a) ∘ id(C)(a) = id(C)(a)
proof
  category_simp
end S
`);
});

test("functoriality and naturality close by the extended set, with the images typed by the instances", () => {
  check(`
section F
variable (η F G C D : Set)
hypothesis functorF : F : C ⥤ D
hypothesis functorG : G : C ⥤ D
hypothesis natural : η : F ⟹ G

theorem functorial (a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c)
  shows F(g ∘ f) ∘ id(D)(F(a)) = F(g) ∘ F(f)
proof
  functor_simp

theorem identities (a ∈ obj(C))
  shows F(id(C)(a)) ∘ F(id(C)(a)) = id(D)(F(a))
proof
  functor_simp

theorem square (a b ∈ obj(C)) (f : a ⟶ b)
  shows η(b) ∘ F(f) = G(f) ∘ η(a)
proof
  functor_simp

theorem squareThenAssoc (a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c)
  shows (η(c) ∘ F(g)) ∘ F(f) = G(g) ∘ (η(b) ∘ F(f))
proof
  calc
    (η(c) ∘ F(g)) ∘ F(f) = (G(g) ∘ η(b)) ∘ F(f) := by rw NaturalTransformation.naturality
    _ = G(g) ∘ (η(b) ∘ F(f)) := by rw Category.assoc

theorem typedImage (a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c)
  shows F(g) ∘ F(f) : F(a) ⟶ F(c)
proof
  synthesize
end F
`);
});

test("the pilot theorems check with the Category root", () => {
  const source = "module CategoryPilot\nimport Grace.Cumulus.Category\n" + `
section S
variable (C : Set)
hypothesis category : Category(C)

theorem unique (a b : Set) (f : a ⟶ b) (g k : b ⟶ a)
  requires gf : g ∘ f = id(C)(a)
  requires fk : f ∘ k = id(C)(b)
  shows g = k
proof
  exact InversePair.unique with *

theorem mono (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  requires gMono : Monomorphism(C, g)
  requires fMono : Monomorphism(C, f)
  shows Monomorphism(C, g ∘ f)
proof
  exact Monomorphism.comp with *
end S
`;
  const result = checkWorkbenchFiles([{ name: "CategoryPilot.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 600));
});
