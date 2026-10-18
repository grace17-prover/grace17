// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, formulaEquals, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = `module RestrictionSyntax
namespace RestrictionSyntax
import Grace.Cumulus.Algebra.Ring.Subring
section Rings
variable (A add zero neg mul one T : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
const expanded = "(T, restrict(add, T × T), zero, restrict(neg, T), restrict(mul, T × T), one)";
const theorem = `theorem laws
  requires ambient : IsCommRing(R)
  requires closed : IsSubring(R, T)
  shows IsCommRing(L)
proof
  exact IsSubring.comm_ring with *
end Rings
end RestrictionSyntax
`;
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "RestrictionSyntax.g17", source }], ["lib"]);
  return kernel;
}

test("restriction scope has exactly the explicit carrier and operation graphs", () => {
  const short = load(header + "notation ring L := R ↾ T\n" + theorem);
  const full = load(header + `notation ring L := ${expanded}\n` + theorem);
  assert.ok(formulaEquals(short.theorems.get("RestrictionSyntax.laws")!, full.theorems.get("RestrictionSyntax.laws")!));
  const a = compileProofModule([exportTheoremForMachine(short, "RestrictionSyntax.laws")]);
  const b = compileProofModule([exportTheoremForMachine(full, "RestrictionSyntax.laws")]);
  assert.deepEqual(a, b);
  verifyProofMachine(short, a);
});

test("restriction syntax cannot supply closure or inherited ring laws", () => {
  assert.throws(() => load(header + "notation ring L := R ↾ T\n" + theorem.replace("  requires closed : IsSubring(R, T)\n", "")), /cannot find evidence.*Subring/);
  assert.throws(() => load(header + `notation ring L := R ↾ T
theorem invalid (x : Set)
  requires ambient : IsCommRing(R)
  requires member : x ∈ L
  shows L[x + 0] = x
proof
  ring
end Rings
end RestrictionSyntax
`), /ring|CommRing|instance|linear arithmetic requires Less/i);
});

test("restriction scope rejects unknown bases and does not escape its section", () => {
  assert.throws(() => load(header + "notation ring L := Missing ↾ T\n" + theorem), /unknown restriction base ring notation Missing/);
  assert.throws(() => load(header + "notation ring L := R ↾ T\nend Rings\ntheorem escaped\n  shows L = L\nproof\n  rfl\nend RestrictionSyntax\n"), /unknown|unbound/i);
});

test("completed and cached goals retain the restricted ring name", () => {
  const source = header + "notation ring L := R ↾ T\n" + theorem;
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "RestrictionSyntax.g17", source }], "ZF", ["RestrictionSyntax.g17"]);
    const checked = result.theorems.find(t => t.name === "RestrictionSyntax.laws");
    assert.ok(checked);
    assert.match(checked.statement, /CommRing\(L\)/);
    assert.match(JSON.stringify(checked.steps), /CommRing\(L\)/);
  }
});
