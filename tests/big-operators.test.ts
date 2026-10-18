// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, loadModuleSourceGraph } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module Sums\nimport Grace.Cumulus.Real.ArithmeticSeries\n\n";

function load(source: string) {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Sums.g17", source }], ["lib"]);
  return kernel;
}

test("∑ k < n, uₖ is the real partial sum and prints as a sum", () => {
  const source = header + `theorem named (A D : Real) (n : Nat)
  shows ∑ k < n, arithmeticTerms(A, D)(k) = realPartialSum(arithmeticTerms(A, D), n)
proof
  rfl

theorem subscript (s : Set) (n : Nat)
  shows (2:R) * (∑ k < n, sₖ) = (2:R) * realPartialSum(s, n)
proof
  rfl
`;
  const kernel = load(source);
  assert.ok(kernel.theorems.has("Sums.named") && kernel.theorems.has("Sums.subscript"));
  const result = checkWorkbenchFiles([{ name: "Sums.g17", source }], "ZFG", ["Sums.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
  const named = result.theorems.find(item => item.name === "Sums.named")!;
  assert.match(named.statement, /∑ k < n, arithmeticTerms\(A, D\)\(k\) = ∑ k < n, arithmeticTerms\(A, D\)\(k\)/);
  const subscript = result.theorems.find(item => item.name === "Sums.subscript")!;
  assert.match(subscript.statement, /2 \* \(∑ k < n, sₖ\)/);
});

test("the body of a sum must apply a sequence to the bound variable", () => {
  assert.throws(() => load(header + `theorem bad (s : Set) (n : Nat)
  shows ∑ k < n, s = realPartialSum(s, n)
proof
  rfl
`), /must apply a sequence to k/);
  assert.throws(() => load(header + `theorem shadow (k s : Set) (n : Nat)
  shows ∑ k < n, sₖ = realPartialSum(s, n)
proof
  rfl
`), /binds a fresh variable/);
});
