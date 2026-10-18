// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";
import { renderTop100 } from "../scripts/update-top-100.ts";

const header = "module CRTRegression\nimport Grace.Cumulus.NumberTheory\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "CRTRegression.g17", source }]);
const integer = (n: number) => `${n < 0 ? "integerNegativeOfNat" : "integerOfNat"}(${Math.abs(n)})`;

test("the public CRT example checks", () => {
  assert.equal(checkWorkbenchFiles([{ name: "ChineseRemainderStarter.g17", source: readFileSync("examples/ChineseRemainderStarter.g17", "utf8") }]).ok, true);
});

test("CRT handles arbitrary signed residues and signed, zero, and unit moduli", () => {
  let source = header;
  for (const [i, [m, n]] of [[3, 5], [-3, 5], [3, -5], [-3, -5], [0, 1], [1, 0], [-1, 0], [1, 1]].entries()) {
    const M = integer(m), N = integer(n);
    source += `theorem signed_${i} (a b : Integer)
  shows ∃ x, Integer(x) ∧ IntegerCongruent(${M}, x, a) ∧ IntegerCongruent(${N}, x, b)
proof
  have coprime : IntegerCoprime(${M}, ${N})
  . unfold IntegerCoprime
    simp [integerGCD, integerNatAbs.ofNat, integerNatAbs.ofNegativeNat]
    compute
  exact ChineseRemainder.exists at ${M}, ${N}, a, b with *
`;
  }
  assert.equal(check(source).ok, true);
});

test("CRT rejects missing coprimality and a missing Bézout identity", () => {
  assert.throws(() => check(header + `theorem invalid (m n a b : Integer)
  shows ∃ x, Integer(x) ∧ IntegerCongruent(m, x, a) ∧ IntegerCongruent(n, x, b)
proof
  exact ChineseRemainder.exists at m, n, a, b with *
`));
  assert.throws(() => check(header + `theorem invalid (m n a b u v : Integer)
  shows IntegerCongruent(m, chineseCombination(m, n, a, b, u, v), a) ∧ IntegerCongruent(n, chineseCombination(m, n, a, b, u, v), b)
proof
  exact chineseCombination.correct at m, n, a, b, u, v with *
`));
});

test("CRT uniqueness is modulo the product, not literal equality", () => {
  const source = readFileSync("examples/ChineseRemainderStarter.g17", "utf8");
  assert.throws(() => checkWorkbenchFiles([{ name: "ChineseRemainderStarter.g17", source: source.replace("shows IntegerCongruent(m * n, x, y)", "shows x = y") }]));
  assert.throws(() => checkWorkbenchFiles([{ name: "ChineseRemainderStarter.g17", source: source.replace("8 = 2 + 3 * 2", "8 = 2 + 3 * 3") }]));
});

test("CRT retains intermediate goal states cold and after editing", () => {
  const file = { name: "NumberTheory/ChineseRemainder.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/ChineseRemainder.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    const proof = result.theorems.find(t => t.name.endsWith("ChineseRemainder.exists"));
    assert.ok(proof?.steps.some(s => s.after.goals.length > 0));
    assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  }
});

test("Top 100 catalogue has current source statements, proof links, and audited counts", () => {
  assert.equal(readFileSync("docs/top-100.md", "utf8"), renderTop100());
  const entries = JSON.parse(readFileSync("docs/top-100.json", "utf8"));
  assert.equal(entries.filter(e => e.status === "verified").length, 52);
  assert.equal(entries.filter(e => e.status === "scoped").length, 0);
  assert.equal(entries.filter(e => e.status === "planned").length, 0);
  assert.ok(!entries.some(e => /Chinese remainder/i.test(e.title)));
});

test("failed CRT edits retain multiplication notation and qualified choice-set names", async () => {
  const { workbenchFailure } = await import("../src/workbench.ts");
  const original = readFileSync("lib/Grace/Cumulus/NumberTheory/ChineseRemainder.g17", "utf8");
  const file = { name: "NumberTheory/ChineseRemainder.g17", source: original };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const incremental of [false, true]) {
    const source = original.replace("  rw [← equation, ← factor]\n  ring\n",
      "  rw [← equation, ← factor]\n  unfold integerMulValue\n  unfold selectedIntegerProduct\n  unfold selectedIntegerProduct.candidates\n  ring\n");
    let failure: ReturnType<typeof workbenchFailure> | undefined;
    try { checkWorkbenchFiles([{ ...file, source }], "ZFG", incremental ? [file.name] : undefined); }
    catch (error) { failure = workbenchFailure(error); }
    assert.ok(failure?.trace, "the intentionally over-unfolded proof must fail with a trace");
    const steps = failure.trace.steps;
    const associative = steps.find(step => step.command === "rw ← factor");
    assert.equal(associative?.after.goals[0]?.goal, "m * n * k = m * (n * k)");
    const chosen = steps.find(step => step.command === "unfold selectedIntegerProduct");
    const goal = chosen?.after.goals[0]?.goal ?? "";
    assert.match(goal, /selectedIntegerProduct\.candidates/);
    assert.doesNotMatch(goal, /(?<!\.)\bcandidates\(/);
    const membership = steps.find(step => step.command === "unfold selectedIntegerProduct.candidates");
    assert.equal(membership?.after.goals[0]?.goal, goal,
      "a Separation membership law cannot rewrite a bare set argument of choose");
  }
});
