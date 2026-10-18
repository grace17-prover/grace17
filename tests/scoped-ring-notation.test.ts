// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine, formulaEquals } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = `module Scoped
import Grace.Cumulus.Algebra.Ring
section Rings
variable (A add zero neg mul one : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
notation ring R := (A, add, zero, neg, mul, one)
`;
const body = `theorem simple (x : Set)
  requires hx : x ∈ A
  shows x * 1 + 0 = x
proof
  ring
end Rings
`;
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Scoped.g17", source }], ["lib"]);
  return kernel;
}
test("scoped notation is exactly the existing operation graph syntax", () => {
  const implicit = load(header + body);
  const explicit = load(header.replace(/notation ring[^\n]*\n/, "") + body.replace("x * 1 + 0", "call2(add, call2(mul, x, one), zero)"));
  assert.ok(formulaEquals(implicit.theorems.get("Scoped.simple")!, explicit.theorems.get("Scoped.simple")!));
  verifyProofMachine(implicit, compileProofModule([exportTheoremForMachine(implicit, "Scoped.simple")]));
});
test("two-ring example supports inference, explicit scopes, and scope restoration", () => {
  const kernel = load(readFileSync("examples/ScopedRingNotation.g17", "utf8"));
  for (const n of ["simplify", "preserves_sum", "explicit_scopes", "preserves_one", "restored"])
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, `ScopedRingNotation.${n}`)]));
});
test("ambiguous carriers require explicit selection", () => {
  assert.throws(() => load(header + `section Other
variable (B plus z minus times unit : Set)
notation ring S := (B, plus, z, minus, times, unit)
theorem ambiguous (x y : Set)
  shows x + y = x + y
proof
  rfl
end Other
end Rings
`), /ambiguous ring notation.*R\[.*S\[/);
});
test("qualified scopes nest without losing other ring names", () => {
  load(header + `section Other
variable (B plus z minus times unit : Set)
notation ring S := (B, plus, z, minus, times, unit)
theorem explicit (x : Set)
  shows S[R[x + 0] + 1] = call2(plus, call2(add, x, zero), unit)
proof
  rfl
end Other
end Rings
`);
});
test("shared hypotheses retain the notation active at their declaration", () => {
  load(header + `hypothesis saved : 0 = zero
section Other
variable (B plus z minus times unit : Set)
notation ring S := (B, plus, z, minus, times, unit)
theorem frozen
  shows zero = zero
proof
  exact saved
end Other
end Rings
`);
});
test("ring notation cannot leak outside its section", () => {
  assert.throws(() => load(header + body + `theorem escaped (x : Set)
  shows R[x] = x
proof
  rfl
`), /unknown variable or constant R/);
});
test("ring notation neither provides membership nor ring laws", () => {
  assert.throws(() => load(header.replace(/hypothesis source[^\n]*\n/, "") + body), /linear arithmetic requires Less|unknown proof Grace\.Cumulus\.Nat\.Order\.Less\.gap/);
});
test("completed and cached goal histories retain ring notation", () => {
  const files = [{ name: "Scoped.g17", source: header + body }];
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles(files, "ZF", ["Scoped.g17"]);
    const theorem = result.theorems.find(t => t.name === "Scoped.simple")!;
    assert.ok(theorem);
    assert.match(theorem.statement, /x \* 1/);
    assert.doesNotMatch(JSON.stringify(theorem.steps), /call2/);
  }
});

test("ring numerals are ring elements, never natural numbers", () => {
  assert.throws(() => load(header + body.replace("x * 1 + 0", "x * 2 + 0")), /different normal forms/);
  load(header + body.replace("x * 1 + 0 = x", "x * 2 + 0 = x + x"));
});
test("scopes reject collisions and declarations outside sections", () => {
  assert.throws(() => load(header.replace("notation ring R", "notation ring A") + body), /already in scope/);
  assert.throws(() => load(header + body.replace("(x : Set)", "(R x : Set)")), /collides/);
  assert.throws(() => load("module Invalid\nnotation ring R := (A, add, zero, neg, mul, one)"), /open theorem section/);
});

test("earlier requirements disambiguate later algebraic requirements", () => {
  load(header + `section Other
variable (B plus z minus times unit : Set)
notation ring S := (B, plus, z, minus, times, unit)
theorem assumed (x y : Set)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires sum : x + y = x
  shows x + y = x
proof
  exact sum
end Other
end Rings
`);
});

test("failed proof histories retain notation without supplying missing membership", () => {
  assert.throws(() => load(header + body.replace("  requires hx : x ∈ A\n", "")), /carrier|membership|ring|polynomial|linear arithmetic/i);
  assert.throws(() => load(header + body.replace("  ring\n", "  exact hx\n")), (error: any) => {
    assert.equal(error.partialTrace?.rings?.[0]?.name, "R");
    return true;
  });
});

test("explicit natural literals override a lexical ring's constants", () => {
  const theorem = `theorem indices (f : Set)
  shows f((0:Nat)) = f((2:Nat)) → f((0:Nat)) = f((2:Nat))
proof
  tauto
end Rings
`;
  const scoped = load(header + theorem);
  const ordinary = load(header.replace(/notation ring[^\n]*\n/, "") + theorem.replaceAll("(0:Nat)", "0").replaceAll("(2:Nat)", "2"));
  assert.ok(formulaEquals(scoped.theorems.get("Scoped.indices")!, ordinary.theorems.get("Scoped.indices")!));
  verifyProofMachine(scoped, compileProofModule([exportTheoremForMachine(scoped, "Scoped.indices")]));
});
