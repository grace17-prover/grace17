// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `notation infixr 70 "∘" => call2(comp(C), _, _) via hypothesis Category(C) for mor(C)`:
// the operation is a template over the pattern variables of a hypothesis in
// scope, the operands' carrier chooses between several, statements and goals
// print with the token, and a calc step justified by one rewrite closes by
// reflexivity.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfgKernel, createZfKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles, rememberFailureDisplay, workbenchFailure } from "../src/workbench.ts";

const header = "module HypothesisNotation\nimport Grace.Cumulus.Category.Functor\n";

function load(source: string, foundation: "ZF" | "ZFG" = "ZF") {
  const kernel = foundation === "ZFG" ? createZfgKernel() : createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "HypothesisNotation.g17", source }], ["lib"]);
  return kernel;
}

const associativity = (conclusion: string) => header + `
theorem assoc (C h g f : Set)
  requires category : Category(C)
  requires hInM : h ∈ mor(C)
  requires gInM : g ∈ mor(C)
  requires fInM : f ∈ mor(C)
  requires outer : dom(C)(h) = cod(C)(g)
  requires inner : dom(C)(g) = cod(C)(f)
  shows ${conclusion}
proof
  exact Category.associative with category, hInM, gInM, fInM, outer, inner
`;

test("g ∘ f is comp(C)(g, f) for the Category hypothesis in scope", () => {
  const written = load(associativity("(h ∘ g) ∘ f = h ∘ (g ∘ f)"));
  const spelled = load(associativity("comp(C)(comp(C)(h, g), f) = comp(C)(h, comp(C)(g, f))"));
  assert.ok(formulaEquals(written.theorems.get("HypothesisNotation.assoc")!, spelled.theorems.get("HypothesisNotation.assoc")!));
});

test("the statement prints with the token and its declared precedence", () => {
  const result = checkWorkbenchFiles([{ name: "HypothesisNotation.g17", source: associativity("(h ∘ g) ∘ f = h ∘ (g ∘ f)") }]);
  assert.equal(result.ok, true);
  const statement = result.theorems.find(item => item.name === "HypothesisNotation.assoc")!.statement;
  assert.match(statement, /\(h ∘ g\) ∘ f = h ∘ g ∘ f$/u);
});

test("a remaining goal and its hypotheses print with the token", () => {
  const source = associativity("(h ∘ g) ∘ f = h ∘ (g ∘ f)")
    .replace("  exact Category.associative with category, hInM, gInM, fInM, outer, inner",
      "  have assoc := Category.associative with category, hInM, gInM, fInM, outer, inner\n  exact hInM");
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "HypothesisNotation.g17", source }], ["lib"]);
    assert.fail("the proof should not check");
  } catch (error) {
    assert.ok(error instanceof SurfaceError);
    rememberFailureDisplay(error, kernel);
    const goal = workbenchFailure(error).trace!.steps.at(-1)!.after.goals[0]!;
    assert.equal(goal.goal, "(h ∘ g) ∘ f = h ∘ g ∘ f");
    assert.equal(goal.locals.find(item => item.name === "assoc")!.formula, "(h ∘ g) ∘ f = h ∘ g ∘ f");
  }
});

const functoriality = (conclusion: string) => header + `
section F
variable (F C D : Set)
hypothesis functor : F : C ⥤ D

theorem image (g f : Set)
  requires gInM : g ∈ mor(C)
  requires fInM : f ∈ mor(C)
  requires composable : dom(C)(g) = cod(C)(f)
  shows ${conclusion}
proof
  exact Functor.comp with functor, gInM, fInM, composable
end F
`;

test("the operands' carrier chooses between the two compositions a functor supplies, and F(f) is map(F)(f)", () => {
  const written = load(functoriality("F(g ∘ f) = F(g) ∘ F(f)"));
  const spelled = load(functoriality("map(F)(comp(C)(g, f)) = comp(D)(map(F)(g), map(F)(f))"));
  assert.ok(formulaEquals(written.theorems.get("HypothesisNotation.image")!, spelled.theorems.get("HypothesisNotation.image")!));
  const result = checkWorkbenchFiles([{ name: "HypothesisNotation.g17", source: functoriality("F(g ∘ f) = F(g) ∘ F(f)") }]);
  assert.equal(result.ok, true);
  assert.match(result.theorems.find(item => item.name === "HypothesisNotation.image")!.statement, /F\(g ∘ f\) = F\(g\) ∘ F\(f\)$/u);
});

test("without a supplying hypothesis the token is rejected, and so are operands that select no composition", () => {
  assert.throws(() => load(header + `
theorem bare (comp g f : Set)
  shows g ∘ f = g ∘ f
proof
  rfl
`), /no hypothesis in scope supplies an operation for ∘/u);
  assert.throws(() => load(header + `
theorem two (C D g f : Set)
  requires first : Category(C)
  requires second : Category(D)
  shows g ∘ f = g ∘ f
proof
  rfl
`), /ambiguous notation ∘/u);
});

test("a calc step justified by one rewrite is complete when the rewrite makes its sides the same", () => {
  const source = associativity("(h ∘ g) ∘ f = h ∘ (g ∘ f)").replace(
    "  exact Category.associative with category, hInM, gInM, fInM, outer, inner",
    `  have assoc := Category.associative with category, hInM, gInM, fInM, outer, inner
  have unit := Category.left_unit with category, fInM
  calc
    (h ∘ g) ∘ f = (h ∘ g) ∘ (id(C)(cod(C)(f)) ∘ f) := by rw unit
    _ = h ∘ (g ∘ (id(C)(cod(C)(f)) ∘ f)) := by rw [unit, assoc]
    _ = h ∘ (g ∘ f) := by rw unit`);
  assert.equal(checkWorkbenchFiles([{ name: "HypothesisNotation.g17", source }]).ok, true);
});

test("a hypothesis pattern names its operation and carriers as terms over its pattern variables", () => {
  for (const declaration of [
    'notation infixr 70 "⋆" => call2(comp(C), _, _) via hypothesis Category(C) for X',
    'notation infixr 70 "⋆" => call2(comp(C), _) via hypothesis Category(C) for mor(C)',
    'notation infixr 70 "⋆" => call2 via hypothesis Category(C) for mor(C)',
    'notation infixr 70 "⋆" => call2(comp(C), _, _) via hypothesis Category(C) for U',
  ]) {
    assert.throws(() => load(header + declaration + "\n"), /hypothesis notation|pattern variables|carrier|operation/u);
  }
});

const ringHeader = "module HypothesisNotation\nimport Grace.Cumulus.Algebra.Ring.FirstIsomorphism\n";

const homs = (body: string) => ringHeader + `
section Homs
variable (f R S : Set)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : f : R →+* S
${body}
end Homs
`;

test("a function form is read off the hypothesis about its argument and prints back with its name", () => {
  const written = load(homs(`
theorem first
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows inducedMap(f) : R ⧸ ker(f) ≃+* S
proof
  exact RingHom.first_isomorphism with *
`));
  const spelled = load(homs(`
theorem first
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows quotientMap(f, R.carrier, S.carrier, quotientRelation(R, ringKernel(f, R.carrier, S.zero))) :
    R ⧸ ringKernel(f, R.carrier, S.zero) ≃+* S
proof
  exact RingHom.first_isomorphism with *
`));
  assert.ok(formulaEquals(written.theorems.get("HypothesisNotation.first")!, spelled.theorems.get("HypothesisNotation.first")!));
  const result = checkWorkbenchFiles([{ name: "HypothesisNotation.g17", source: homs(`
theorem first
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows quotientMap(f, R.carrier, S.carrier, quotientRelation(R, ringKernel(f, R.carrier, S.zero))) :
    R ⧸ ringKernel(f, R.carrier, S.zero) ≃+* S
proof
  exact RingHom.first_isomorphism with *
`) }]);
  assert.equal(result.ok, true);
  assert.match(result.theorems.find(item => item.name === "HypothesisNotation.first")!.statement,
    /→ RingIso\(inducedMap\(f\), R ⧸ ker\(f\), S\)$/u);
});

test("a function form of one name is read off whichever hypothesis is about its argument, a variable of the name wins, and with no hypothesis the error names the shapes", () => {
  // The same spelling ker(f) under a group homomorphism is the group kernel.
  const kernel = load("module HypothesisNotation\nimport Grace.Cumulus.Algebra.Group.Kernel\n" + `
theorem trivial (f G H : Set)
  requires hom : f : G →* H
  shows G.one ∈ ker(f)
proof
  exact GroupHom.one_mem_kernel with hom
`);
  const spelled = load("module HypothesisNotation\nimport Grace.Cumulus.Algebra.Group.Kernel\n" + `
theorem trivial (f G H : Set)
  requires hom : f : G →* H
  shows G.one ∈ kernel(f, G, H)
proof
  exact GroupHom.one_mem_kernel with hom
`);
  assert.ok(formulaEquals(kernel.theorems.get("HypothesisNotation.trivial")!, spelled.theorems.get("HypothesisNotation.trivial")!));
  // Two homomorphisms in scope: each kernel is read off its own hypothesis.
  const two = load(ringHeader + `
theorem both (f g R S T : Set)
  requires first : f : R →+* S
  requires second : g : S →+* T
  shows ker(f) ⊆ R.carrier ∧ ker(g) ⊆ S.carrier
proof
  constructor
  . exact RingHom.kernel_subset with first
  . exact RingHom.kernel_subset with second
`);
  const bothSpelled = load(ringHeader + `
theorem both (f g R S T : Set)
  requires first : f : R →+* S
  requires second : g : S →+* T
  shows ringKernel(f, R.carrier, S.zero) ⊆ R.carrier ∧ ringKernel(g, S.carrier, T.zero) ⊆ S.carrier
proof
  constructor
  . exact RingHom.kernel_subset with first
  . exact RingHom.kernel_subset with second
`);
  assert.ok(formulaEquals(two.theorems.get("HypothesisNotation.both")!, bothSpelled.theorems.get("HypothesisNotation.both")!));
  // A variable named ker is applied as a function.
  const variable = load(ringHeader + `
theorem applied (ker f R S : Set)
  requires hom : f : R →+* S
  shows ker(f) = ker(f)
proof
  rfl
`);
  const applied = load(ringHeader + `
theorem applied (ker f R S : Set)
  requires hom : f : R →+* S
  shows apply(ker, f) = apply(ker, f)
proof
  rfl
`);
  assert.ok(formulaEquals(variable.theorems.get("HypothesisNotation.applied")!, applied.theorems.get("HypothesisNotation.applied")!));
  assert.throws(() => load(ringHeader + `
theorem bare (f : Set)
  shows ker(f) = ker(f)
proof
  rfl
`), /no hypothesis in scope supplies ker\(f\); it needs one of RingHom/u);
  assert.throws(() => load(ringHeader + `
theorem other (f g R S : Set)
  requires hom : f : R →+* S
  shows ker(g) = ker(g)
proof
  rfl
`), /no hypothesis in scope supplies ker\(f\)/u);
});

test("a function form with free parameters chooses between hypotheses by the carrier its arguments lie in", () => {
  const metricHeader = "module HypothesisNotation\nimport Grace.Cumulus.Metric.Spaces\n";
  const written = load(metricHeader + `
section Iso
variable (f X Y : Set)
hypothesis isometry : Isometry(f, X, Y)

theorem preserved (x y : X)
  shows d(f(x), f(y)) = d(x, y)
proof
  exact Isometry.dist with *
end Iso
`, "ZFG");
  const spelled = load(metricHeader + `
section Iso
variable (f X Y : Set)
hypothesis isometry : Isometry(f, X, Y)

theorem preserved (x y : X)
  shows Y.dist(f(x), f(y)) = X.dist(x, y)
proof
  exact Isometry.dist with *
end Iso
`, "ZFG");
  assert.ok(formulaEquals(written.theorems.get("HypothesisNotation.preserved")!, spelled.theorems.get("HypothesisNotation.preserved")!));
  assert.throws(() => load(metricHeader + `
section Iso
variable (f X Y : Set)
hypothesis isometry : Isometry(f, X, Y)

theorem unplaced (a b : Set)
  shows d(a, b) = d(a, b)
proof
  rfl
end Iso
`, "ZFG"), /ambiguous notation d\(a, b\)/u);
});
