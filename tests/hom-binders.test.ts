// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `notation mixfix "_ : _ ⟶ _" => Morphism(C, _, _, _) via hypothesis
// Category(C) for obj(C), mor(C)`: a binder `(f : a ⟶ b)` and a formula
// `f : a ⟶ b` read the category off a hypothesis in scope, the guard opens
// to its conjuncts for `with *`, `assumption`, `typecheck`, and `cc`,
// composites and identities are synthesized, statements and goals print the
// form back, and the ambiguous and unsupplied cases are reported.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles, rememberFailureDisplay, workbenchFailure } from "../src/workbench.ts";

const header = "module HomBinders\nimport Grace.Cumulus.Category.Functor\n";

const category = (body: string) => header + `
section S
variable (C : Set)
hypothesis category : Category(C)
${body}
end S
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "HomBinders.g17", source }], ["lib"]);
  return kernel;
}

test("(f : a ⟶ b) is the guard Morphism(C, f, a, b) of the category in scope", () => {
  const written = load(category(`
theorem guard (a b : Set) (f : a ⟶ b)
  shows f ∈ mor(C)
proof
  assumption
`));
  const spelled = load(header + `
theorem guard (C a b f : Set)
  requires fHom : Morphism(C, f, a, b)
  requires category : Category(C)
  shows f ∈ mor(C)
proof
  exact Morphism.in_morphisms with fHom
`);
  assert.ok(formulaEquals(written.theorems.get("HomBinders.guard")!, spelled.theorems.get("HomBinders.guard")!));
});

test("the guard's conjuncts and hom-set membership are available to with *, typecheck, and cc", () => {
  const source = category(`
theorem closed (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows g ∘ f ∈ mor(C)
proof
  exact Category.comp_closed with *

theorem endpoints (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows dom(C)(g) = cod(C)(f)
proof
  cc

theorem homSet (a b : Set) (f : a ⟶ b)
  shows f ∈ hom(C, a, b)
proof
  typecheck

theorem objects (a b : Set) (f : a ⟶ b)
  shows a ∈ obj(C)
proof
  typecheck

theorem composite (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows g ∘ f ∈ mor(C)
proof
  typecheck
`);
  const result = checkWorkbenchFiles([{ name: "HomBinders.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 400));
});

test("composites and identities are synthesized from the guards of their factors", () => {
  const source = category(`
theorem composite (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows g ∘ f : a ⟶ c
proof
  synthesize

theorem unit (a : Set)
  requires aInO : a ∈ obj(C)
  shows id(C)(a) : a ⟶ a
proof
  synthesize

theorem applied (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows (g ∘ f) ∘ id(C)(a) = g ∘ f
proof
  exact Category.id_right with *
`);
  assert.equal(checkWorkbenchFiles([{ name: "HomBinders.g17", source }]).ok, true);
});

test("statements, assumptions, and locals print the form back, with the guard on its quantifier", () => {
  const source = category(`
theorem left (a b : Set) (f : a ⟶ b)
  shows id(C)(b) ∘ f = f
proof
  category_simp
`);
  const result = checkWorkbenchFiles([{ name: "HomBinders.g17", source }]);
  assert.equal(result.ok, true);
  const statement = result.theorems.find(item => item.name === "HomBinders.left")!.statement;
  assert.equal(statement, "∀ C a b, ∀ (f : a ⟶ b), Category(C) → C.id(b) ∘ f = f");
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "HomBinders.g17", source: category(`
theorem open (a b c : Set) (f : a ⟶ b) (g : b ⟶ c)
  shows id(C)(c) ∘ (g ∘ f) = g ∘ f
proof
  have gf : g ∘ f : a ⟶ c by synthesize
  exact gf
`) }], ["lib"]);
    assert.fail("the proof should not check");
  } catch (error) {
    assert.ok(error instanceof SurfaceError);
    rememberFailureDisplay(error, kernel);
    const goal = workbenchFailure(error).trace!.steps.at(-1)!.after.goals[0]!;
    assert.deepEqual(goal.assumptions.slice(0, 2), ["f : a ⟶ b", "g : b ⟶ c"]);
    assert.equal(goal.locals.find(item => item.name === "gf")!.formula, "g ∘ f : a ⟶ c");
  }
});

test("a functor supplies both categories; object binders select the source, and F applied to a morphism is a morphism of the target", () => {
  const source = header + `
section F
variable (F C D : Set)
hypothesis functor : F : C ⥤ D

theorem image (a b ∈ obj(C)) (f : a ⟶ b)
  shows F(f) : F(a) ⟶ F(b)
proof
  exact Functor.map_hom with *
end F
`;
  const result = checkWorkbenchFiles([{ name: "HomBinders.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 400));
  const statement = result.theorems.find(item => item.name === "HomBinders.image")!.statement;
  assert.equal(statement, "∀ F C D, ∀ a b ∈ C.obj, ∀ (f : a ⟶ b), Functor(F, C, D) → (F(f) : F(a) ⟶ F(b))");
  const spelled = load(source.replace("shows F(f) : F(a) ⟶ F(b)", "shows Morphism(D, map(F)(f), obj(F)(a), obj(F)(b))"));
  assert.ok(formulaEquals(load(source).theorems.get("HomBinders.image")!, spelled.theorems.get("HomBinders.image")!));
});

test("without object evidence a functor's two categories are ambiguous, and without a hypothesis the form is rejected", () => {
  assert.throws(() => load(header + `
section F
variable (F C D : Set)
hypothesis functor : F : C ⥤ D
theorem ambiguous (a b : Set) (f : a ⟶ b)
  shows f = f
proof
  rfl
end F
`), /ambiguous notation _ : _ ⟶ _.*\(a ∈ C\.obj\)/u);
  assert.throws(() => load(header + `
theorem bare (f a b : Set)
  requires h : f : a ⟶ b
  shows f = f
proof
  rfl
`), /no hypothesis in scope supplies the notation _ : _ ⟶ _; it needs one of Category, Functor/u);
});

test("an instance may fix a variable by a hypothesis-shaped premise, and only by one", () => {
  assert.equal(checkWorkbenchFiles([{ name: "HomBinders.g17", source: category(`
instance triple (a b c d : Set) (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  shows (h ∘ g) ∘ f : a ⟶ d
proof
  synthesize
`) }]).ok, true);
  assert.throws(() => load(header + `
instance loose (A B x : Set)
  requires h : x ∈ B
  shows x ∈ A
proof
  sorry
`), /instance variables must occur in its conclusion or in a hypothesis-shaped premise; unconstrained: B/u);
});
