// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Ergonomics met while proving the Banach–Tarski paradox: a `by` runs every
// tactic of its `;`-sequence in calc steps and local facts, a numeral
// coefficient in a real linear_combination is the real numeral, linarith
// reads division by a numeral and ring says a quotient is an atom, a `have`
// proposition may begin on the next line, a section hypothesis may continue
// on the next line, unfold reaches a predicate under the connectives and
// binders, `rw fact with args` rewrites with the instance, simp reduces
// nested projections to a fixed point, a vector component's realness is
// found whatever else is imported or loaded, a theorem outside the
// import closure is reported with its module, a wrong step in a
// defunique proof is reported at its line with the proof state reached,
// a numeral under an overloaded prefix is read by the sort of the
// position it sits in, a comparison of function values is read in the
// sort their typing theorems give, `rfl` in a disjunction pattern
// substitutes its equation, a substitution renames a capturing binder,
// and membership induction names the Foundation lemmas in full.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createSetTheoryKernel, createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";

const real = "module ProvingErgonomics\nimport Grace.Cumulus.Real.Inverse\nimport Grace.Cumulus.Real.Natural\n";

function check(source: string): void {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "ProvingErgonomics.g17", source }], ["lib"]);
}

function failure(source: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "ProvingErgonomics.g17", source }], ["lib"]);
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    return error.message;
  }
  assert.fail("the module should not check");
}

test("by runs every tactic of a ;-sequence in a calc step and in a one-line have", () => {
  check(real + `
theorem calcSequence (a b : Real)
  requires h : a = b
  shows a + a = b + b
proof
  calc
    a + a = 2 * a := by ring
    _ = 2 * b := by rw h; ring
    _ = b + b := by ring

theorem haveSequence (a b : Real)
  requires h : a = b
  shows a + a = b + b
proof
  have doubled : a + a = 2 * b by rw h; ring
  rw doubled
  ring
`);
});

test("a trailing by on a theorem still rejects a sequence with a clear message", () => {
  const message = failure(real + `
theorem trailing (x : Set)
  shows x = x by rfl; rfl
`);
  assert.match(message, /trailing by expects exactly one tactic; write a proof block for a sequence/u);
});

test("a numeral coefficient in a real linear_combination is the real numeral", () => {
  check(real + `
def dotValue (u : Set) : Set := u

theorem scaled (a b : Real)
  requires h : a = b
  shows 2 * a = 2 * b
proof
  linear_combination 2 * h

theorem scaledDifference (a b : Real)
  requires h : a = b
  shows 2 * a - 2 * b = 0
proof
  linear_combination 2 * h

theorem productCoefficient (a b u : Set)
  requires ha : a ∈ ℝ
  requires hb : b ∈ ℝ
  requires hu : dotValue(u) ∈ ℝ
  requires h : a = b
  shows 2 * dotValue(u) * a = 2 * dotValue(u) * b
proof
  linear_combination 2 * dotValue(u) * h

theorem indexedCoefficient (a b : Real) (u : Set)
  requires hu : u : 3 → ℝ
  requires h : a = b
  shows u(2) * a = u(2) * b
proof
  linear_combination u(2) * h
`);
});

test("linarith reads division by a numeral", () => {
  check(real + `
theorem halfPositive (x : Real)
  requires h : 0 < x
  shows 0 < x / 2
proof
  linarith

theorem halvesOrdered (x y : Real)
  requires h : x < y
  shows x / 2 < y / 2
proof
  linarith

theorem halves (x : Real)
  shows x / 2 + x / 2 = x
proof
  linarith

theorem midpoint (x y : Real)
  requires h : x ≤ y
  shows (x + y) / 2 ≤ y
proof
  linarith

theorem thirds (x : Real)
  requires h : 0 < x
  shows x / 3 < x / 2
proof
  linarith
`);
});

test("ring says that a quotient by a numeral is an atom", () => {
  const message = failure(real + `
theorem halvesByRing (x : Real)
  shows x / 2 + x / 2 = x
proof
  ring
`);
  assert.match(message, /different normal forms; a quotient t \/ k is an atom for ring: for a linear goal use linarith/u);
  assert.match(message, /realDiv\.eq_mul_inv or a named constant such as oneHalf/u);
});

test("a have proposition may begin on the next, more indented line", () => {
  check(real + `
theorem haveNext (a b : Real)
  requires h : a = b
  shows a = b
proof
  have same :
      a = b
    exact h
  exact same

theorem haveNextBy (a b : Real)
  requires h : a = b
  shows b = a
proof
  have same :
      a = b by exact h
  rw same
  rfl
`);
});

test("unfold reaches a defined predicate under the connectives and binders", () => {
  check(real + `
predicate Same (x : Set) := x = x

theorem underAnd (a b : Set)
  shows Same(a) ∧ Same(b)
proof
  unfold Same
  constructor
  . rfl
  . rfl

theorem underImplication (a b : Set)
  shows Same(a) → Same(b)
proof
  unfold Same
  intro h
  rfl

theorem underForall (A : Set)
  shows ∀ x ∈ A, Same(x)
proof
  unfold Same
  intros x hx
  rfl

theorem underExists (A a : Set)
  requires ha : a ∈ A
  shows ∃ x ∈ A, Same(x) ∧ Same(a)
proof
  unfold Same
  witness a
  constructor
  . exact ha
  . constructor
    . rfl
    . rfl
`);
  const message = failure(real + `
predicate Same (x : Set) := x = x

theorem nothing (a : Set)
  shows a = a ∨ a = a
proof
  unfold Same
`);
  assert.match(message, /unfold Same finds nothing to unfold in the goal a = a ∨ a = a/u);
});

test("rw with an applied fact rewrites with the instance, and an inapplicable list is explained", () => {
  check(real + `
theorem rewriteWith (f X p : Set)
  requires moves : ∀ q, q ∈ X → f(q) = q
  requires hp : p ∈ X
  shows f(p) = p
proof
  rw moves with p, hp
`);
  const message = failure(real + `
theorem rewriteWithBad (f X p : Set)
  requires moves : ∀ q, q ∈ X → f(q) = q
  requires hp : p ∈ X
  shows f(p) = p
proof
  rw moves with p, zzz
`);
  assert.match(message, /^line 10: rw takes a fact or rule, optionally applied with `at terms` and `with facts`/u);
  assert.match(message, /`rw moves with p, zzz` rewrites with moves applied to p, zzz, which failed: /u);
  assert.doesNotMatch(message, /unknown settle rule/u);
});

test("simp with projection lemmas reduces nested projections to a fixed point", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "ProvingErgonomics.g17", source: `module ProvingErgonomics
import Grace.Cumulus.Set.Tuple

theorem nestedMembership (a b c A : Set)
  requires ha : a ∈ A
  shows fst(fst(((a, b), c))) ∈ A
proof
  simp [fst.pair, snd.pair]
  exact ha

theorem nestedFact (a b c A : Set)
  requires h : snd(fst(((a, b), c))) ∈ A
  shows b ∈ A
proof
  simp [fst.pair, snd.pair] at h
  exact h
` }], ["lib"]);
});

test("a theorem outside the import closure is reported with its module", () => {
  const library = failure("module ProvingErgonomics\nimport Grace.Cumulus.Real.Ring\n" + `
theorem outside (A : Real)
  shows A = A
proof
  exact realDiv.eq_mul_inv
`);
  assert.equal(library, "line 7: unknown proof realDiv.eq_mul_inv; the library declares it as realDiv.eq_mul_inv " +
    "in module Grace.Cumulus.Real.Inverse, which this module does not import");
  // A bare name is not matched against the dotted declarations that end in
  // it: `distinct` suggests nothing, and says that no fact has the name.
  const bare = failure(`module Bare
import Grace.Cumulus.Algebra.Ring.Core
theorem probe
  shows 1 = 1
proof
  exact distinct
`);
  assert.equal(bare, "line 6: unknown proof distinct; no local fact of this proof and no declaration in scope has this name");
  // A module loaded in the same environment but not imported is reported from the environment.
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Loaded.g17", source: "module Loaded\nimport Grace.Cumulus.Real.Inverse\n" }], ["lib"]);
  try {
    loadModuleSourceGraph(kernel, [{ file: "ProvingErgonomics.g17", source: "module ProvingErgonomics\nimport Grace.Cumulus.Real.Ring\n" + `
theorem outside (A : Real)
  shows A = A
proof
  exact realDiv.eq_mul_inv
` }], ["lib"]);
    assert.fail("the module should not check");
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    assert.match(error.message, /unknown proof realDiv\.eq_mul_inv; it is declared as Grace\.Cumulus\.Real\.Inverse\.realDiv\.eq_mul_inv in module Grace\.Cumulus\.Real\.Inverse, which this module does not import/u);
  }
});

// The realness of a vector component u(k), with u : 3 → ℝ and k ∈ 3, is
// found by the typing rules whether the module is checked alone, after the
// rotation freeness module is loaded, or with that module imported: the
// specific rule f(x) ∈ B is tried before the general x ∈ ℝ rules it brings.
const component = (extraImport: string) => `module ProvingErgonomics
import Grace.Cumulus.Geometry.Vectors3
${extraImport}
theorem componentReal (u : Set) (k : Set)
  requires vectorU : u : 3 → ℝ
  requires hk : k ∈ 3
  shows u(k) ∈ ℝ
proof
  typecheck

theorem componentIdentity (u v : Set) (k : Set)
  requires vectorU : u : 3 → ℝ
  requires vectorV : v : 3 → ℝ
  requires hk : k ∈ 3
  shows (u(k):R) * (v(k):R) + (u(k):R) * (v(k):R) = 2 * ((v(k):R) * (u(k):R))
proof
  ring

theorem componentCombination (u v : Set) (k : Set)
  requires vectorU : u : 3 → ℝ
  requires vectorV : v : 3 → ℝ
  requires hk : k ∈ 3
  requires h : (u(k):R) = (v(k):R)
  shows (u(k):R) * (u(k):R) = (v(k):R) * (u(k):R)
proof
  linear_combination (u(k):R) * h
`;

test("a vector component's realness does not depend on what else is loaded or imported", () => {
  const alone = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleSourceGraph(alone, [{ file: "ProvingErgonomics.g17", source: component("") }], ["lib"]);
  const preloaded = createSetTheoryKernel({ profile: "ZFG" });
  const freeness = "lib/Grace/Cumulus/Rotation/Freeness.g17";
  loadModuleSourceGraph(preloaded, [{ file: freeness, source: readFileSync(freeness, "utf8") }], ["lib"]);
  loadModuleSourceGraph(preloaded, [{ file: "ProvingErgonomics.g17", source: component("") }], ["lib"]);
  const imported = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleSourceGraph(imported, [{ file: "ProvingErgonomics.g17", source: component("import Grace.Cumulus.Rotation.Freeness") }], ["lib"]);
});

test("a wrong step in a defunique existence or uniqueness proof is located with a partial trace", () => {
  const source = (existence: string, uniqueness: string) => "module ProvingErgonomics\nimport Grace.Cumulus.Set.Core\n" + `
defunique only (A : Set) (y ∈ singleton(A)) := y = A
proof
${existence}
uniqueness
${uniqueness}
`;
  const good = ["  witness A\n  constructor\n  . simp [singleton.membership]\n  . rfl",
    "  intros u hu first v hv second\n  rw [first, second]\n  rfl"];
  check(source(good[0]!, good[1]!));
  for (const [existence, uniqueness, line, what] of [
    ["  witness A\n  constructor\n  . exact A\n  . rfl", good[1]!, 8, "existence"],
    [good[0]!, "  intros u hu first v hv second\n  exact first", 12, "uniqueness"],
  ] as const) {
    const kernel = createZfKernel();
    try {
      loadModuleSourceGraph(kernel, [{ file: "ProvingErgonomics.g17", source: source(existence, uniqueness) }], ["lib"]);
      assert.fail("the module should not check");
    } catch (error) {
      assert.ok(error instanceof SurfaceError, String(error));
      assert.equal(error.line, line, error.message);
      assert.match(error.message, new RegExp(`^line ${line}: defunique only needs a checked ${what} proof: `, "u"));
      assert.ok(error.partialTrace, "the failure carries the proof state reached");
      assert.ok(error.partialTrace.steps.length > 0, "the trace has the steps before the failure");
    }
  }
});

// The integers, rationals, and reals each declare a prefix `-`, and a
// numeral fits every one of them; the position decides.
const numbers = "module ProvingErgonomics\nimport Grace.Cumulus.Combinatorics.DerangementCount\nimport Grace.Cumulus.Probability.Uniform\n";

test("a numeral under an overloaded prefix is read by the sort of the parameter it fills", () => {
  check(numbers + `
theorem probe (n k : Nat)
  shows integerPow(-1, k) * integerOfNat(n) = integerPow(-1, k) * integerOfNat(n)
proof
  rfl
`);
});

test("a numeral under an overloaded infix or prefix is read by the sort of the other operand", () => {
  check(numbers + `
theorem integerStep (n : Nat)
  shows integerOfNat(n) - 1 = integerOfNat(n) - 1
proof
  rfl

theorem realStep (n : Nat)
  shows realNat(n) - 1 = realNat(n) - 1
proof
  rfl

theorem realFactor (n : Nat)
  shows realNat(n) * -1 = realNat(n) * -1
proof
  rfl
`);
});

test("an annotation fixes the sort of a negated numeral, and Z names the integers", () => {
  check(numbers + `
theorem annotated
  shows (-1 : Z) = (-1 : ℤ) ∧ (-1 : Integer) = (-1:Z)
proof
  split
  rfl
  rfl
`);
});

test("a negated numeral whose position fixes no sort is rejected with the candidates and the annotations", () => {
  const message = failure(numbers + `
theorem loose
  shows -1 = -1
proof
  rfl
`);
  assert.match(message, /cannot resolve notation - on the numeral 1: it could be the Integer, Rational, or Real one/);
  assert.match(message, /annotate it, as in \(-1:Z\), \(-1:Q\), or \(-1:R\)/);
});

const realCore = "module ProvingErgonomics\nimport Grace.Cumulus.Real.Core\n";

test("a comparison of function values is read in the sort their typing theorem gives", () => {
  // rationalCut.real types rationalCut(q) as a real, so the order is the
  // real one in a premise and in a have type alike; before, both fell
  // through to the natural order without a word.
  check(realCore + `
theorem cutOrder (p q : Rational)
  requires h : rationalCut(p) < rationalCut(q)
  shows (rationalCut(p):R) < (rationalCut(q):R)
proof
  have again : rationalCut(p) < rationalCut(q) := h
  exact again
`);
  const message = failure(realCore + `
theorem cutNatural (p q : Rational)
  requires h : rationalCut(p) < rationalCut(q)
  shows Less(rationalCut(p), rationalCut(q))
proof
  exact h
`);
  assert.match(message, /proof establishes relates\(realLess, rationalCut\(p\), rationalCut\(q\)\)/);
});

test("a numeral beside a typed function value is read in the value's sort", () => {
  check("module ProvingErgonomics\nimport Grace.Cumulus.Real.Natural\n" + `
theorem cutZero (p : Rational)
  requires h : rationalCut(p) < 0
  shows (rationalCut(p):R) < (0:R)
proof
  exact h
`);
});

test("a function value typed in several carriers needs an annotation on a comparison", () => {
  const message = failure(realCore + `
def twice (q : Set) : Set := q

theorem twice.real (q : Set)
  requires h : Real(q)
  shows Real(twice(q))
proof
  unfold twice
  exact h

theorem twice.rational (q : Set)
  requires h : Rational(q)
  shows Rational(twice(q))
proof
  unfold twice
  exact h

theorem loose (a b : Set)
  requires h : twice(a) < twice(b)
  shows twice(a) < twice(b)
proof
  exact h
`);
  assert.match(message, /cannot resolve notation < between twice\(a\) and twice\(b\): twice\(a\) could be the Rational one or the Real one/);
  assert.match(message, /annotate it, as in \(twice\(a\):Q\) or \(twice\(a\):R\)/);
});

const sets = "module ProvingErgonomics\nimport Grace.Cumulus.Set\n";

test("rfl in a disjunction pattern substitutes its equation", () => {
  check(sets + `
theorem alternatives (x y A : Set)
  requires h : x = y ∨ ∃ z, z ∈ A ∧ x = z
  shows x = y ∨ ∃ z, z ∈ A ∧ x = z
proof
  rcases h with rfl | ⟨z, hz, rfl⟩
  . left
    rfl
  . right
    witness z
    exact ⟨hz, rfl⟩

theorem twoWay (x y : Set)
  requires h : x = y ∨ y = x
  shows x = y
proof
  cases h with rfl | rfl
  . rfl
  . rfl

theorem packed (a b c d : Set)
  requires h : (a, b) = (c, d)
  shows a = c ∧ b = d
proof
  obtain ⟨rfl, rfl⟩ := orderedPair.injective with h
  exact ⟨rfl, rfl⟩
`);
  const message = failure(sets + `
theorem noVariable (A B C : Set)
  requires h : A ∪ B = B ∪ C ∨ A = B
  shows A ∪ B = B ∪ C ∨ A = B
proof
  rcases h with rfl | rfl
  . left
    rfl
  . right
    rfl
`);
  assert.match(message, /rfl needs a variable to substitute, and neither side of A ∪ B = B ∪ C is one/);
});

test("a substitution renames a goal binder that would capture the replacement", () => {
  // W := V under a binder named V used to be skipped without a word; the
  // binder is renamed and the body substituted, by rfl and by rw under.
  check(sets + `
theorem captured (W V U B g : Set)
  requires shape : (W, V) = (V, U)
  requires h : ∀ V, V ∈ B → g(U) ⊆ g(V)
  shows ∀ V, V ∈ B → g(W) ⊆ g(V)
proof
  obtain ⟨rfl, rfl⟩ := orderedPair.injective with shape
  exact h

theorem capturedRewrite (W V B g : Set)
  requires same : W = V
  requires h : ∀ U, U ∈ B → g(V) ⊆ g(U)
  shows ∀ V, V ∈ B → g(W) ⊆ g(V)
proof
  rw under same
  exact h
`);
});

test("membership induction names the Foundation lemmas in full beside a topological closure", () => {
  check("module ProvingErgonomics\nimport Grace.Cumulus.Set.Foundation\nimport Grace.Cumulus.Topology.Space\n" + `
theorem notSelf (x : Set)
  shows ¬x ∈ x
proof
  induction x using membership
  intros current ih hSelf
  have impossible := ih at current with hSelf, hSelf
  exact impossible
`);
});
