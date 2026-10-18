// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, theoremDependencies } from "../src/index.ts";

const identity = `module UniqueTest
namespace UniqueTest
import Grace.Cumulus.Set.Basic
defunique identity (A : Set) (x ∈ {A}) := x = A
proof
  witness A
  refine ⟨singleton.self at A, rfl⟩
uniqueness
  intro x
  intro xMember
  intro xValue
  intro y
  intro yMember
  intro yValue
  cc
`;
const check = (source: string) => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "UniqueTest.g17", source: source + "\nend UniqueTest\n" }], ["lib"]);
  return kernel;
};

test("unique definitions elaborate and retain only ZF dependencies", () => {
  const kernel = check(identity);
  for (const suffix of ["exists", "unique", "selected"]) {
    const name = `UniqueTest.identity.${suffix}`;
    kernel.checkProof(kernel.theoremProofs.get(name)!);
    assert.ok(theoremDependencies(kernel, name).axioms.every(a => !/choice/i.test(a)));
  }
});

test("generated unique-definition locals avoid user names", () => {
  for (const name of ["value", "item", "sourceMember", "property", "uniqueOther"]) {
    assert.doesNotThrow(() => check(identity.replaceAll("A", name)));
  }
});

test("unique definitions reject missing and false uniqueness or existence", () => {
  assert.throws(() => check(identity.slice(0, identity.indexOf("uniqueness"))), /uniqueness/);
  assert.throws(() => check(identity.replace("  cc", "  rfl")));
  assert.throws(() => check(identity.replace("witness A", "witness empty")));
  const nonunique = identity.replace("(A : Set)", "(A B : Set)")
    .replace("(x ∈ {A}) := x = A", "(x ∈ {A, B}) := x = x")
    .replace("singleton.self at A", "pair.left at A, B");
  assert.throws(() => check(nonunique));
});

test("unique selection preserves requirements", () => {
  const conditional = identity.replace("(x ∈ {A}) := x = A", "(x ∈ A) := x = A\nrequires self : A ∈ A")
    .replace("singleton.self at A", "self");
  check(conditional + `\ntheorem guarded (A : Set)
  requires self : A ∈ A
  shows identity(A) ∈ A ∧ identity(A) = A
proof
  exact identity.selected at A with self
`);
  assert.throws(() => check(conditional + `\ntheorem unguarded (A : Set)
  shows identity(A) ∈ A
proof
  have selected := identity.selected at A with *
  tauto
`));
});

test("integer arithmetic and CRT check with Choice absent", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "IntegerZFRegression.g17", source:
    "module IntegerZFRegression\nimport Grace.Cumulus.Int\nimport Grace.Cumulus.NumberTheory\n" }], ["lib"]);
  assert.equal(kernel.axioms.has("set.globalChoice"), false);
  for (const name of kernel.theorems.keys()) {
    if (/\.Int\.|\.NumberTheory\./.test(name)) {
      assert.ok(theoremDependencies(kernel, name).axioms.every(a => !/choice/i.test(a)), name);
    }
  }
});
