// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module IntegerRingRegression\nimport Grace.Cumulus.Int\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "IntegerRingRegression.g17", source }]);

test("integer ring handles signed polynomials, nested subtraction, and units", () => {
  assert.equal(checkWorkbenchFiles([{ name: "IntegerRingStarter.g17", source: readFileSync("examples/IntegerRingStarter.g17", "utf8") }]).ok, true);
});

test("integer, natural and rational ring goals select their own carriers", () => {
  assert.equal(check(header + `import Grace.Cumulus.Rat

theorem ints (x y : Integer)
  shows (x - y) * (x + y) = x * x - y * y
proof
  ring

theorem nats (x y : Nat)
  shows (x + y) * (x + y) = x * x + x * y + y * x + y * y
proof
  ring

theorem rats (x y : Rational)
  shows (x - y) * (x + y) = x * x - y * y
proof
  ring
`).ok, true);
});

test("integer ring rejects a false sign, missing carrier evidence, and illicit cancellation", () => {
  for (const [type, statement] of [
    ["Integer", "(-x) * (-y) = -(x * y)"],
    ["Set", "integerAddValue(x, y) = integerAddValue(y, x)"],
    ["Integer", "x * y = x"],
  ]) assert.throws(() => check(header + `theorem incorrect (x y : ${type})
  shows ${statement}
proof
  ring
`));
});

test("checked notation bridges support user-defined value presentations", () => {
  assert.equal(check(header + `
def customSum (x y : Integer) : Integer := integerAddValue(x, y)
theorem customSum.notation (x y : Integer)
  shows call2(integerAdd, x, y) = customSum(x, y)
proof
  unfold customSum
  exact integerAddValue.notation at x, y with *

theorem custom (x y : Integer)
  shows customSum(x, y) = customSum(y, x)
proof
  ring
`).ok, true);
});

test("a notation theorem with an extra premise cannot bypass its guard", () => {
  const source = header + `
def guardedSum (x y : Set) : Set := integerAddValue(x, y)
theorem guardedSum.notation (x y : Integer)
  requires equal : x = y
  shows call2(integerAdd, x, y) = guardedSum(x, y)
proof
  unfold guardedSum
  exact integerAddValue.notation at x, y with *

theorem unsupported (x y : Integer)
  shows guardedSum(x, y) = guardedSum(y, x)
proof
  ring
`;
  assert.throws(() => check(source));
});

test("integer ring retains intermediate goals on cold and edited checks", () => {
  const file = { name: "IntegerRingRegression.g17", source: header + `
theorem staged (x y : Integer)
  shows (x + y) - y = x
proof
  have typed : Integer(x)
  . assumption
  ring
` };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    const proof = result.theorems.find(t => t.name.endsWith("staged"));
    assert.ok(proof?.steps.some(s => s.after.goals.length > 0));
    assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  }
});

test("integer normalization and linear combinations reuse the same checked interface", () => {
  assert.equal(check(header + `
theorem normalized (x y : Integer)
  shows (x + y) * (x - y) = x * x - y * y
proof
  ring_nf

theorem rearranged (x y z : Integer)
  requires equality : x + y = z
  shows x = z - y
proof
  linear_combination equality
`).ok, true);
});
