// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module IntegerRegression\nimport Grace.Cumulus.NumberTheory\n";

test("all-integer GCD and the signed example check through the public import", () => {
  assert.equal(checkWorkbenchFiles([{ name: "IntegerGCDStarter.g17", source: readFileSync("examples/IntegerGCDStarter.g17", "utf8") }]).ok, true);
});

test("absolute value is independent of noncanonical natural-pair representatives", () => {
  let source = header;
  for (const [a, b] of [[7, 11], [2, 6], [17, 12], [10, 5], [7, 7], [0, 0]]) {
    const n = Math.abs(a - b), negative = a < b;
    source += `theorem magnitude_${a}_${b}
  shows integerNatAbs(integerClass(${a}, ${b})) = ${n}
proof
  have integer := integerClass.integer at ${a}, ${b} with *
  have difference : ${negative ? `${a} + ${n} = ${b}` : `${b} + ${n} = ${a}`}
  . compute
  have shape := integerClass.${negative ? "negative" : "positive"}_difference at ${a}, ${b}, ${n} with *
  apply integerNatAbs.eq_of_sign at integerClass(${a}, ${b}), ${n} with *{2}
  ${negative ? "right" : "left"}
  exact shape
`;
  }
  assert.equal(checkWorkbenchFiles([{ name: "IntegerRegression.g17", source }]).ok, true);
});

test("signed GCD handles every sign combination and both zero inputs", () => {
  const signed = (n: number) => `${n < 0 ? "integerNegativeOfNat" : "integerOfNat"}(${Math.abs(n)})`;
  let source = header;
  for (const [index, [a, b, g]] of [[252, 198, 18], [-252, 198, 18], [252, -198, 18], [-252, -198, 18], [0, -37, 37], [-37, 0, 37], [0, 0, 0]].entries()) {
    source += `theorem gcd_${index}
  shows integerGCD(${signed(a)}, ${signed(b)}) = ${g}
proof
  simp [integerGCD, integerNatAbs.ofNat, integerNatAbs.ofNegativeNat]
  compute
`;
  }
  assert.equal(checkWorkbenchFiles([{ name: "IntegerRegression.g17", source }]).ok, true);
});

test("wrong signs and missing carrier hypotheses are rejected", () => {
  const example = readFileSync("examples/IntegerGCDStarter.g17", "utf8");
  assert.throws(() => checkWorkbenchFiles([{ name: "IntegerGCDStarter.g17", source: example.replace("integerNegativeOfNat(4) * integerNegativeOfNat(252)", "integerOfNat(4) * integerNegativeOfNat(252)") }]));
  assert.throws(() => checkWorkbenchFiles([{ name: "IntegerRegression.g17", source: header + `theorem missing_types (x y : Set)
  shows IsIntegerGCD(x, y, integerGCD(x, y))
proof
  exact integerGCD.correct at x, y with *
` }]));
});

test("signed Bézout retains intermediate goal states after an edit", () => {
  const file = { name: "NumberTheory/IntegerGCD.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/IntegerGCD.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edited signed identity\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    const proof = result.theorems.find(t => t.name.endsWith("integerGCD.bezout"));
    assert.ok(proof?.steps.some(s => s.after.goals.length > 0));
    assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  }
});
