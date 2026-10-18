// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module ExtendedRegression\nimport Grace.Cumulus.NumberTheory\n";

test("the public extended-GCD example computes and certifies quotient integers", () => {
  assert.equal(checkWorkbenchFiles([{ name: "ExtendedGCDStarter.g17", source: readFileSync("examples/ExtendedGCDStarter.g17", "utf8") }]).ok, true);
});

// Independent host-side Euclidean recurrence supplies signed expected values.
function extended(a: number, b: number): [number, number] {
  let u = 1, v = 0, nextU = 0, nextV = 1;
  while (b !== 0) {
    const q = Math.floor(a / b);
    [a, b] = [b, a - q * b];
    [u, nextU] = [nextU, u - q * nextU];
    [v, nextV] = [nextV, v - q * nextV];
  }
  return [u, v];
}

test("computed signed components agree with an independent algorithm on boundary and nontrivial inputs", () => {
  const inputs = [[0, 0], [0, 37], [37, 0], [24, 54], [54, 24], [37, 37], [144, 89], [252, 198], [101, 37], [21, 100]];
  let source = header;
  for (const [a, b] of inputs) {
    for (const [index, coefficient] of extended(a, b).entries()) {
      const first = index === 0 ? "Bool.true" : "Bool.false";
      // Compare differences, without assuming canonical representatives.
      source += `theorem value_${a}_${b}_${index}
  shows bezoutComponent(${b}, ${a}, ${b}, Bool.false, ${first}) + ${Math.max(-coefficient, 0)} = ${Math.max(coefficient, 0)} + bezoutComponent(${b}, ${a}, ${b}, Bool.true, ${first})
proof
  compute
`;
    }
  }
  assert.equal(checkWorkbenchFiles([{ name: "ExtendedRegression.g17", source }]).ok, true);
});

test("an incorrect computed sign is rejected", () => {
  const source = readFileSync("examples/ExtendedGCDStarter.g17", "utf8")
    .replace("shows bezoutRight(252, 198) = integerNegativeOfNat(5)", "shows bezoutRight(252, 198) = integerOfNat(5)")
    .replace("unfold integerNegativeOfNat", "unfold integerOfNat")
    .replace("bezoutRight.representatives at 252, 198, 0, 5", "bezoutRight.representatives at 252, 198, 5, 0");
  assert.throws(() => checkWorkbenchFiles([{ name: "ExtendedGCDStarter.g17", source }]));
});

test("the coefficient invariant also covers deliberately truncated runs", () => {
  const source = header + `theorem truncated (a b : Nat)
  shows integerLinearCombination(bezoutLeftSteps(0, a, b), bezoutRightSteps(0, a, b), a, b) = integerOfNat(gcdSteps(0, a, b))
proof
  exact bezoutSteps.correct at 0, a, b with *
`;
  assert.equal(checkWorkbenchFiles([{ name: "ExtendedRegression.g17", source }]).ok, true);
});

test("the executable induction proof retains goal states cold and after editing", () => {
  const file = { name: "NumberTheory/ExtendedGCD.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/ExtendedGCD.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  const start = performance.now();
  const first = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  const checked = performance.now();
  assert.equal(first.ok, true);
  const proof = first.theorems.find(t => t.name.endsWith("bezoutSteps.correct"));
  assert.ok(proof?.steps.some(s => s.after.goals.length > 0));
  assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  file.source += "\n-- edited coefficient invariant\n";
  const edited = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  assert.equal(edited.ok, true);
  assert.ok(edited.theorems.find(t => t.name.endsWith("bezoutSteps.correct"))?.steps.some(s => s.after.goals.length > 0));
  console.log(`Extended-GCD leaf: cold ${(checked-start).toFixed(1)} ms; edited ${(performance.now()-checked).toFixed(1)} ms`);
});

test("recursive arithmetic notation uses the pending signature without bypassing structural admission", () => {
  const source = `module RecursiveNotation\nimport Grace.Cumulus.Int
 def doubled (n : Nat) → Nat
  | zero => 0
  | succ(n) => doubled(n) + doubled(n) + 2
 theorem value
  shows doubled(8) = 510
 proof
  compute
`.replace(/^ /gm, "");
  assert.equal(checkWorkbenchFiles([{ name: "RecursiveNotation.g17", source }]).ok, true);
  assert.throws(() => checkWorkbenchFiles([{ name: "RecursiveNotation.g17", source: source.replace("doubled(n) + doubled(n)", "doubled(succ(n)) + doubled(n)") }]));
});
