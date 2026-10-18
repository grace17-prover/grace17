// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, compileProofModule, exportTheoremForMachine, verifyProofMachine, auditTheoremAxioms } from "../src/index.ts";
const prefix = `module Constants
namespace Constants
import Grace.Cumulus.Algebra.Ring
section Rings
variable (A add z neg mul one B plus o minus times unit T : Set)
notation ring R := (A, add, z, neg, mul, one)
notation ring S := (B, plus, o, minus, times, unit)
notation ring L := R ↾ T
`;
const suffix = "end Rings\nend Constants\n";
function load(body: string) {
  const k = createZfKernel();
  loadModuleSourceGraph(k, [{ file: "Constants.g17", source: prefix + body + suffix }], ["lib"]);
  return k;
}
for (const structure of ["IsRing", "IsCommRing"]) {
  test(`typecheck proves both constants from a local ${structure} certificate`, () => {
    const k = load(`hypothesis ring : ${structure}(R)
theorem constants
  shows R[0] ∈ R ∧ R[1] ∈ R
proof
  constructor
  . typecheck
  . typecheck
`);
    const name = "Constants.constants";
    const program = compileProofModule([exportTheoremForMachine(k, name)]);
    verifyProofMachine(k, program);
    const audit = auditTheoremAxioms(k, name);
    assert.equal(audit.complete, true);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), []);
  });
}

test("typecheck uses a locally derived ring and selects the requested carrier", () => {
  const k = load(`hypothesis ring : IsCommRing(R)
hypothesis other : IsCommRing(S)
theorem local
  requires source : IsCommRing(L) ∧ IsCommRing(S)
  shows L[0] ∈ L ∧ S[1] ∈ S
proof
  have localRing := IsCommRing.ring with source.left
  constructor
  . typecheck
  . typecheck
`);
  verifyProofMachine(k, compileProofModule([exportTheoremForMachine(k, "Constants.local")]));
});

for (const [name, hypothesis, goal] of [
  ["missing certificate", "", "R[0] ∈ R"],
  ["wrong carrier", "hypothesis ring : IsCommRing(R)\n", "R[0] ∈ S"],
  ["unproved restriction", "hypothesis ring : IsCommRing(R)\n", "L[0] ∈ L"],
  ["arbitrary element", "hypothesis ring : IsCommRing(R)\n", "T ∈ R"],
]) {
  test(`typecheck ring constants rejects ${name}`, () => {
    assert.throws(() => load(`${hypothesis}theorem invalid\n  shows ${goal}\nproof\n  typecheck\n`), /typecheck could not infer/);
  });
}

test("a previous theorem's ring evidence does not leak into the next theorem", () => {
  assert.throws(() => load(`theorem first
  requires ring : IsCommRing(R)
  shows R[0] ∈ R
proof
  typecheck
theorem second
  shows R[0] ∈ R
proof
  typecheck
`), /typecheck could not infer/);
});
