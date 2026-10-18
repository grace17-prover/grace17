// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module GCDRegression\nimport Grace.Cumulus.NumberTheory\n";

test("GCD certificates check through the public number-theory import", () => {
  const source = readFileSync("examples/GCDStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "GCDStarter.g17", source }]).ok, true);
});

test("Euclidean GCD proofs retain goal traces cold and after editing", () => {
  const file = { name: "NumberTheory/GCD.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/GCD.g17", "utf8") };
  const start = performance.now();
  prepareWorkbenchFiles([file], "ZFG", file.name);
  const prepared = performance.now();
  const first = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  const checked = performance.now();
  assert.equal(first.ok, true);
  const forward = first.theorems.find(t => t.name.endsWith("IsGCD.euclidean_forward"));
  assert.ok(forward?.steps.some(s => s.after.goals.length > 0));
  assert.equal(forward?.steps.at(-1)?.after.goals.length, 0);
  file.source += "\n-- edited Euclidean proof\n";
  const edited = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  assert.equal(edited.ok, true);
  assert.ok(edited.theorems.find(t => t.name.endsWith("IsGCD.euclidean_forward"))?.steps.some(s => s.after.goals.length > 0));
  console.log(`GCD timings: prepare ${(prepared-start).toFixed(1)} ms; cold ${(checked-prepared).toFixed(1)} ms; edited ${(performance.now()-checked).toFixed(1)} ms`);
});

test("GCD rules reject missing mathematical side conditions", () => {
  for (const body of [
    `theorem missing_summand (d a b : Nat)
  requires sum : d ∣ a + b
  shows d ∣ b
proof
  exact divides.add_cancel_left at d, a, b with *`,
    `theorem missing_equation (a b q r g : Nat)
  requires gcd : IsGCD(b, r, g)
  shows IsGCD(a, b, g)
proof
  exact IsGCD.euclidean_backward at a, b, q, r, g with *`,
    `theorem common_is_not_greatest (a b g : Nat)
  requires left : g ∣ a
  requires right : g ∣ b
  shows IsGCD(a, b, g)
proof
  exact IsGCD.intro at a, b, g with *`,
    `theorem zero_multiple_bound (a : Nat)
  shows a ≤ 0
proof
  have zero := divides.zero at a with *
  exact divides.le at a, 0 with *`,
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "GCDRegression.g17", source: header + body }]));
});

test("a wrong Euclidean remainder fails its arithmetic certificate", () => {
  const source = readFileSync("examples/GCDStarter.g17", "utf8").replace("have start : 252 = 198 * 1 + 54", "have start : 252 = 198 * 1 + 55");
  assert.throws(() => checkWorkbenchFiles([{ name: "GCDStarter.g17", source }]));
});

test("executable GCD handles zero inputs, unequal inputs, and consecutive Fibonacci inputs", () => {
  for (const [a, b, expected] of [[0, 0, 0], [0, 37, 37], [37, 0, 37], [24, 54, 6], [54, 24, 6], [144, 89, 1]]) {
    const source = header + `theorem value\n  shows gcd(${a}, ${b}) = ${expected}\nproof\n  compute\n`;
    assert.equal(checkWorkbenchFiles([{ name: "GCDRegression.g17", source }]).ok, true);
  }
});

test("Euclidean correctness retains goals cold and after an edit", () => {
  const file = { name: "NumberTheory/Euclidean.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/Euclidean.g17", "utf8") };
  const start = performance.now();
  prepareWorkbenchFiles([file], "ZFG", file.name);
  const prepared = performance.now();
  const first = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  const checked = performance.now();
  assert.equal(first.ok, true);
  assert.ok(first.theorems.find(t => t.name.endsWith("gcdSteps.correct"))?.steps.some(s => s.after.goals.length > 0));
  file.source += "\n-- edited arbitrary-input correctness proof\n";
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  console.log(`Euclidean timings: prepare ${(prepared-start).toFixed(1)} ms; cold ${(checked-prepared).toFixed(1)} ms; edited ${(performance.now()-checked).toFixed(1)} ms`);
});

test("remainder and iteration bounds are necessary", () => {
  for (const body of [
    `theorem zero_divisor (n : Nat)
  shows n % 0 < 0
proof
  exact mod.less at n, 0 with *`,
    `theorem insufficient_steps
  shows IsGCD(12, 8, gcdSteps(0, 12, 8))
proof
  exact gcdSteps.correct at 0, 12, 8 with *`,
    `theorem wrong_answer
  shows gcd(54, 24) = 12
proof
  compute`,
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "GCDRegression.g17", source: header + body }]));
});
