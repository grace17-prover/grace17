// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { canonical, createZfKernel, createZfgKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = (imports: string) => `module Numerals
${imports}
section Rings
variable (A add zero neg mul one : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
notation ring R := (A, add, zero, neg, mul, one)
`;

function load(source: string, foundation: "ZF" | "ZFG" = "ZF") {
  const kernel = foundation === "ZF" ? createZfKernel() : createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Numerals.g17", source }], ["lib"]);
  return kernel;
}

test("ring adds, multiplies, and cancels numeral coefficients in a scoped ring", () => {
  const kernel = load(header("import Grace.Cumulus.Algebra.Ring") + `theorem double (x : Set)
  requires hx : x ∈ A
  shows x + x = 2 * x
proof
  ring

theorem expand (x : Set)
  requires hx : x ∈ A
  shows (x + 1) * (x + 1) = x * x + 2 * x + 1
proof
  ring

theorem cancel (x y : Set)
  requires hx : x ∈ A
  requires hy : y ∈ A
  shows x - 3 * x + 2 * y = 2 * y - 2 * x
proof
  ring

theorem scaled (x y : Set)
  requires hx : x ∈ A
  requires hy : y ∈ A
  shows (2 * x) * (3 * y) = 6 * (x * y)
proof
  ring

theorem constants
  shows 2 * 3 + 1 = 7
proof
  ring
end Rings
`);
  for (const name of ["double", "expand", "cancel", "scaled", "constants"]) {
    const full = `Numerals.${name}`;
    assert.ok(kernel.theorems.has(full), full);
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, full)]));
  }
});

test("numerals above one elaborate to ringNat and display as numerals", () => {
  const source = header("import Grace.Cumulus.Algebra.Ring") + `theorem triple (x : Set)
  requires hx : x ∈ A
  shows 3 * x = x + x + x
proof
  ring
end Rings
`;
  const result = checkWorkbenchFiles([{ name: "Numerals.g17", source }], "ZF", ["Numerals.g17"]);
  assert.equal(result.ok, true, result.message);
  const theorem = result.theorems.find(item => item.name === "Numerals.triple")!;
  assert.match(theorem.statement, /3 \* x = x \+ x \+ x/);
  assert.doesNotMatch(theorem.statement, /ringNat/);
});

test("a numeral above one needs the numeral module", () => {
  assert.throws(() => load(header("import Grace.Cumulus.Algebra.Ring.Core") + `theorem double (x : Set)
  requires hx : x ∈ A
  shows x + x = 2 * x
proof
  ring
end Rings
`), /numeral 2 needs ringNat/);
});

test("real numerals come from one template and work with ring and linarith", () => {
  const kernel = load(`module Numerals
import Grace.Cumulus.Real

theorem three_real
  shows Real((3:R))
proof
  typecheck

theorem double (x : Real)
  shows x + x = (2:R) * x
proof
  ring

theorem sum
  shows (2:R) + 2 = (4:R)
proof
  ring

theorem bound (x : Real)
  requires large : (3:R) ≤ x
  shows (5:R) < x + x
proof
  linarith
`, "ZFG");
  for (const name of ["three_real", "double", "sum", "bound"]) assert.ok(kernel.theorems.has(`Numerals.${name}`), name);
  const source = `module Numerals
import Grace.Cumulus.Real

theorem seven
  shows (3:R) + 4 = (7:R)
proof
  ring
`;
  const result = checkWorkbenchFiles([{ name: "Numerals.g17", source }], "ZFG", ["Numerals.g17"]);
  assert.equal(result.ok, true, result.message);
  const theorem = result.theorems.find(item => item.name === "Numerals.seven")!;
  assert.match(theorem.statement, /3 \+ 4 = 7/);
  assert.doesNotMatch(theorem.statement, /ringNat/);
});

// A bare literal inside a ring section is the ring's numeral, except beside
// an operand placed in ℕ, and an annotated natural literal fixes its
// operation as the natural one.
test("a literal beside an operand placed in ℕ is natural inside a ring section", () => {
  const kernel = load(header("import Grace.Cumulus.Algebra.Ring\nimport Grace.Cumulus.Cardinal.Enumeration") + `
theorem annotated (j : Nat)
  shows (2:N) * j = j + j
proof
  sorry

theorem byBinder (j : Nat)
  shows 2 * j = j * 2
proof
  sorry

theorem byFact (n : Set)
  requires natural : Nat(n)
  shows 1 ≤ n ↔ ¬ n = 0
proof
  sorry

theorem byRule (S : Set)
  shows 2 ≤ cardinality(S) ∨ cardinality(S) = 0
proof
  sorry

theorem byEquation (n : Set) (cs : List(A))
  requires size : n = length{A}(cs)
  shows 1 ≤ n ∨ n = 0
proof
  sorry

theorem byResultSort (cs ds : List(A), j : Nat)
  shows (length{A}(cs) + length{A}(ds)) - (2 * j) ≤ length{A}(cs) + length{A}(ds)
proof
  sorry

theorem ringElements (x : Set)
  requires hx : x ∈ A
  shows x + 1 = 1 + x ∧ x * 2 = 2 * x ∧ (x = 0 ∨ 1 ≤ 2 ∨ 2 * 3 = 3 * 2)
proof
  sorry
end Rings
`, "ZFG");
  const statement = (name: string): string => canonical(kernel.theorems.get(`Numerals.${name}`)!);
  // The section's zero and one occur once each, in the IsCommRing hypothesis.
  const occurrences = (statement: string, name: string): number =>
    statement.split(`{"name":"${name}","tag":"var"}`).length - 1;
  for (const name of ["annotated", "byBinder", "byFact", "byRule", "byEquation", "byResultSort"]) {
    assert.doesNotMatch(statement(name), /ringNat"|call2"/, name);
    assert.equal(occurrences(statement(name), "zero"), 1, name);
    assert.equal(occurrences(statement(name), "one"), 1, name);
    assert.match(statement(name), /Nat\.Rec\.(add|mul)"|Nat\.Rec\.sub"|LessEqual"/, name);
  }
  const ring = statement("ringElements");
  assert.match(ring, /call2"/);
  assert.match(ring, /ringNat"/);
  assert.ok(occurrences(ring, "zero") > 1);
  assert.ok(occurrences(ring, "one") > 1);
  assert.doesNotMatch(ring, /Nat\.Rec\.(add|mul)"/);
});

// The bound of a `defunique`, `(m ∈ ℕ)`, places the value in ℕ for the
// notation around it, inside its section and outside, so the literals
// beside it are natural; and a bare literal read as a ring numeral is
// rejected beside a comparison operand that is placed nowhere.
test("a defunique's bound places its value, and a ring numeral beside an " +
  "unplaced comparison operand is an error", () => {
  const imports = "import Grace.Cumulus.Algebra.Ring\n" +
    "import Grace.Cumulus.Cardinal.Enumeration";
  const kernel = load(header(imports) + `
defunique rm (cs : List(A)) (r : Set) (m ∈ ℕ) := m = m
requires center : r ∈ A
proof
  sorry
uniqueness
  sorry

theorem byBound (r : Set) (cs : List(A))
  requires center : r ∈ A
  shows 2 ≤ rm(cs, r) ∧ rm(cs, r) = 1 ∧ rm(cs, r) + 1 ≤ length{A}(cs)
proof
  sorry

theorem ringElement (x : Set)
  requires hx : x ∈ A
  shows x < 1 ∨ x = 0
proof
  sorry
end Rings

theorem outsideBound (A add zero neg mul one r cs : Set)
  shows 2 ≤ rm(A, add, zero, neg, mul, one, cs, r) ∨
    rm(A, add, zero, neg, mul, one, cs, r) = 0
proof
  sorry
`, "ZFG");
  const statement = (name: string): string =>
    canonical(kernel.theorems.get(`Numerals.${name}`)!);
  const occurrences = (statement: string, name: string): number =>
    statement.split(`{"name":"${name}","tag":"var"}`).length - 1;
  // The section's zero and one are arguments of rm; the literals beside
  // its values are the natural numerals.
  const inside = statement("byBound");
  assert.doesNotMatch(inside, /ringNat"|call2"/);
  assert.match(inside, /"tag":"nat","value":"2"/);
  assert.match(inside, /"tag":"nat","value":"1"/);
  assert.match(inside, /LessEqual"/);
  assert.match(inside, /Nat\.Rec\.add"/);
  const outside = statement("outsideBound");
  assert.doesNotMatch(outside, /ringNat"/);
  assert.match(outside, /"tag":"nat","value":"2"/);
  assert.match(outside, /"tag":"nat","value":"0"/);
  assert.match(outside, /LessEqual"/);
  // A ring element beside a literal keeps the ring's numeral.
  const element = statement("ringElement");
  assert.equal(occurrences(element, "one"), 2);
  assert.equal(occurrences(element, "zero"), 2);
  assert.throws(() => load(header("import Grace.Cumulus.Algebra.Ring") + `
def f (x : Set) : Set := x

theorem stray (x : Set)
  shows 2 ≤ f(x)
proof
  sorry
end Rings
`, "ZFG"), /cannot read 2 ≤ f\(A, add, zero, neg, mul, one, x\): 2 is the numeral of the ring R and f\(A, add, zero, neg, mul, one, x\) is placed in no ring and in no sort; write \(2:N\) ≤ f\(A, add, zero, neg, mul, one, x\) for the natural order, or R\[2\] ≤ f\(A, add, zero, neg, mul, one, x\) to compare the ring's numeral/);
});
