// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled rings: a ring is a structure R with projections R.carrier, R.add,
// R.zero, R.neg, R.mul, R.one; under a hypothesis CommRing(R) the
// operations are written x + y, x * y, -x, a binder (x : R) is membership
// in the carrier, R[0], R[1], R[2] are the ring's constants and numerals,
// `ring` reads the operation graphs off the structure, statements print
// back in the same notation, the bridges relate the bundled and
// parameterized forms, and the parameterized ring scopes keep working with
// the bundled predicates in scope.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createZfKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BundledRings\nimport Grace.Cumulus.Algebra.Ring\n";

const section = (body: string) => header + `
section S
variable (R : Set)
hypothesis ring : CommRing(R)
${body}
end S
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledRings.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledRings.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name === name)!.statement;

test("x + y, x * y, -x, R[0], and (x : R) are the projections of the structure applied", () => {
  const written = load(section(`
theorem spelled (x y : R)
  shows -x + x + x * y + R[0] = R[1] * (x * y)
proof
  ring
`));
  const explicit = load(header + `
theorem spelled (R x y : Set)
  requires xIn : x ∈ Ring.carrier(R)
  requires yIn : y ∈ Ring.carrier(R)
  requires ring : CommRing(R)
  shows call2(Ring.add(R), call2(Ring.add(R), call2(Ring.add(R), apply(Ring.neg(R), x), x), call2(Ring.mul(R), x, y)), Ring.zero(R)) =
    call2(Ring.mul(R), Ring.one(R), call2(Ring.mul(R), x, y))
proof
  ring
`);
  assert.ok(formulaEquals(written.theorems.get("BundledRings.spelled")!, explicit.theorems.get("BundledRings.spelled")!));
});

test("ring, ring_nf, and linear_combination read the operation graphs off the bundled hypothesis, with numerals", () => {
  const result = check(section(`
theorem square (x y : R)
  shows (x + y) * (x + y) = x * x + R[2] * (x * y) + y * y
proof
  ring

theorem numerals
  shows R[1] + R[1] = R[2] ∧ R[2] * R[3] = R[6]
proof
  constructor
  . ring
  . ring

theorem combined (x y : R)
  requires h : x + y = R[0]
  shows x * x = y * y
proof
  linear_combination (x + -y) * h

theorem normalized (x : R)
  requires h : x + x = x * R[2]
  shows x * R[2] = x + x
proof
  ring_nf at h
  ring_nf
`));
  assert.equal(statement(result, "BundledRings.square"),
    "∀ R, ∀ (x y : R), CommRing(R) → (x + y) * (x + y) = x * x + R[2] * (x * y) + y * y");
  assert.equal(statement(result, "BundledRings.numerals"), "∀ R, CommRing(R) → R.one + R.one = R[2] ∧ R[2] * R[3] = R[6]");
});

test("x - y is Ring.sub(R, x, y), the addition of the negation, and prints back as x - y", () => {
  const written = load(section(`
theorem minus (x y : R)
  shows x - y = x + (-y)
proof
  exact Ring.sub.value with *
`));
  const spelled = load(section(`
theorem minus (x y : R)
  shows Ring.sub(R, x, y) = call2(R.add, x, apply(R.neg, y))
proof
  exact Ring.sub.value with *
`));
  assert.ok(formulaEquals(written.theorems.get("BundledRings.minus")!, spelled.theorems.get("BundledRings.minus")!));
  const result = check(section(`
theorem minus (x y : R)
  shows x - y = x + (-y) ∧ x - y ∈ R
proof
  constructor
  . exact Ring.sub.value with *
  . exact Ring.sub_mem with *
`));
  assert.equal(result.theorems.find(item => item.name === "BundledRings.minus")!.statement,
    "∀ R, ∀ (x y : R), CommRing(R) → x - y = x + (-y) ∧ x - y ∈ R");
});

test("memberships of compound terms are synthesized from the closure instances, and with * reads the unbundled laws", () => {
  check(section(`
theorem closed (x y : R)
  shows (x + y) * -x + R[2] ∈ R.carrier
proof
  typecheck

theorem swap (x y : R)
  shows x * y = y * x
proof
  have comm := CommRing.parts with ring
  exact IsCommRing.mul_comm with comm, *

theorem bundledIsRing
  shows Ring(R)
proof
  exact CommRing.to_ring with ring
`));
});

test("the bridges relate the structure to the parameterized predicates, and Ring.intro takes the typing and the parents", () => {
  const result = check(header + `
theorem toParts (R : Set)
  requires field : Field(R)
  shows IsField(R.carrier, R.add, R.zero, R.neg, R.mul, R.one) ∧ CommRing(R) ∧ IsRing(R.carrier, R.add, R.zero, R.neg, R.mul, R.one)
proof
  have isField := Field.parts with field
  have comm := Field.to_comm_ring with field
  have parts := Ring.parts with (CommRing.to_ring with comm)
  refine ⟨isField, comm, parts⟩

theorem fromParts (A add zero neg mul one : Set)
  requires comm : IsCommRing(A, add, zero, neg, mul, one)
  shows CommRing(Ring.mk(A, add, zero, neg, mul, one)) ∧ Ring.carrier(Ring.mk(A, add, zero, neg, mul, one)) = A
proof
  constructor
  . exact CommRing.of_parts with comm
  . ring_projections

theorem ordered (A add zero neg mul one inv lt : Set)
  requires ordered : IsOrderedField(A, add, zero, neg, mul, one, inv, lt)
  shows OrderedField(Ring.mk(A, add, zero, neg, mul, one), lt)
proof
  exact OrderedField.of_parts with ordered
`);
  assert.ok(result.ok);
  const kernel = load(header);
  const basic = "Grace.Cumulus.Algebra.Ring.Basic.";
  assert.equal(kernel.predicates.get(`${basic}Ring`), 1);
  assert.equal(kernel.predicates.get(`${basic}CommRing`), 1);
  assert.equal(kernel.predicates.get("Grace.Cumulus.Algebra.Ring.Defs.IsCommRing"), 6);
  for (const name of ["Ring.mk.carrier", "Ring.mk.one", "Ring.mk.data", "Ring.eta", "Ring.intro", "Ring.parts", "CommRing.parts", "Field.parts", "OrderedField.parts"]) {
    assert.ok(kernel.theorems.has(basic + name), name);
  }
  let intro = kernel.theorems.get(`${basic}Ring.intro`)!;
  const bound: string[] = [];
  while (intro.tag === "forall") { bound.push(intro.variable); intro = intro.body; }
  assert.deepEqual(bound, ["carrier", "add", "zero", "neg", "mul", "one"]);
  const premises: string[] = [];
  while (intro.tag === "imp") { if (intro.left.tag === "pred") premises.push(intro.left.pred.split(".").at(-1)!); intro = intro.right; }
  assert.deepEqual(premises, ["FunctionBetween", "in", "FunctionBetween", "FunctionBetween", "in",
    "AbelianGroup", "Monoid", "Distributive"]);
});

test("the integers become a bundled value, and the section theorem instantiates at it with the same notation", () => {
  const result = check(readFileSync("examples/BundledRings.g17", "utf8"));
  assert.equal(statement(result, "BundledRings.square_sum.integers"),
    "∀ x y ∈ integerRing.carrier, (x + y) * (x + y) = x * x + integerRing[2] * (x * y) + y * y");
  assert.equal(statement(result, "BundledRings.integerRing.comm_ring"), "CommRing(integerRing)");
});

test("a parameterized ring scope keeps its shorthand with the bundled predicates in scope, and a bare + falls back to the naturals", () => {
  const kernel = load(header + `
section P
variable (A add zero neg mul one : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
notation ring R := (A, add, zero, neg, mul, one)

theorem scoped (x : Set)
  requires hx : x ∈ A
  requires comm : IsCommRing(R)
  shows x * 1 + 0 = x
proof
  ring
end P
`);
  let formula = kernel.theorems.get("BundledRings.scoped")!;
  while (formula.tag === "forall") formula = formula.body;
  const hypotheses: string[] = [];
  while (formula.tag === "imp") { if (formula.left.tag === "pred") hypotheses.push(`${formula.left.pred.split(".").at(-1)}/${formula.left.args.length}`); formula = formula.right; }
  assert.deepEqual(hypotheses.filter(item => item.startsWith("IsCommRing")), ["IsCommRing/6", "IsCommRing/6"]);
  const bare = load(header + `
theorem bare (x y : Set)
  shows x + y = y + x
proof
  sorry
`);
  const natural = load(header + `
theorem bare (x y : Set)
  shows add(x, y) = add(y, x)
proof
  sorry
`);
  assert.ok(formulaEquals(bare.theorems.get("BundledRings.bare")!, natural.theorems.get("BundledRings.bare")!));
});
