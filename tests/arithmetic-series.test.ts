// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module SeriesRegression\nimport Grace.Cumulus.Real.ArithmeticSeries\n";

test("arithmetic series public examples include empty and singleton prefixes", () => {
  const source = readFileSync("examples/ArithmeticSeriesStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "ArithmeticSeriesStarter.g17", source }]).ok, true);
});

test("arithmetic series survives cold and edited workbench checks", () => {
  const file = { name: "Real/ArithmeticSeries.g17", source: readFileSync("lib/Grace/Cumulus/Real/ArithmeticSeries.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  file.source += "\n-- edited series proof\n";
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
});

test("series formulas reject wrong counts and missing realness", () => {
  for (const body of [
    `theorem wrong_count (A D : Real, n : Nat)
  shows ((1:R) + (1:R)) * (realPartialSum(arithmeticTerms(A, D), n):R) =
    ((realNat(n):R) + (1:R)) * (((1:R) + (1:R)) * A + (realNat(n):R) * D)
proof
  exact arithmeticSeries.inclusive at A, D, n with *`,
    `theorem wrong_odd (n : Nat)
  shows realPartialSum(arithmeticTerms(realOne, (1:R) + (1:R)), n) =
    (realNat(n):R) * (realNat(n):R) + (1:R)
proof
  exact arithmeticSeries.odd_sum at n with *`,
    `theorem missing_realness (A D : Set, n : Nat)
  shows RealSequence(arithmeticTerms(A, D))
proof
  exact arithmeticTerms.sequence at A, D with *`,
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "SeriesRegression.g17", source: header + body }]));
});
