// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import {
  app, compileProofMachine, compute, createZfgKernel, elaborateModule, encodeProofMachineBinary,
  eq, evaluateNative, exportTheorem, formulaEquals, loadModuleGraph, nat, nativeValueToTerm,
  rationalClassCompute, termEquals, v,
} from "../src/index.ts";

const arithmetic = `
define plus (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(plus(x, y))
notation infixl 60 "+" => plus

define times (x y : Nat) -> Nat
  | zero, y => zero
  | succ(x), y => y + times(x, y)
notation infixl 70 "*" => times

theorem compact.ground
  shows 7 * 100 = 700
proof
  compute
`;

test("kernel computation certificates replay admitted recursion without reduction trees", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, arithmetic);
  const proof = kernel.theoremProofs.get("compact.ground")!;
  const statement = kernel.theorems.get("compact.ground")!;
  assert.equal(proof.rule, "compute");
  assert.equal(formulaEquals(kernel.checkProof(proof), statement), true);
  assert.equal(exportTheorem(kernel, "compact.ground").proof.nodes.length, 1);
});

test("kernel rejects forged computation results and dependency lists", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, arithmetic);
  const original = kernel.theoremProofs.get("compact.ground")!;
  assert.equal(original.rule, "compute");
  if (original.rule !== "compute") return;

  assert.throws(() => kernel.checkProof(compute(original.left, app("zero"), original.definitions)), /different normal forms/);
  assert.throws(() => kernel.checkProof(compute(original.left, original.right, ["times"])), /different normal forms|inexact definition dependency/);
  assert.throws(() => kernel.checkProof(compute(original.left, original.right, [...original.definitions, "unknown"])), /Unknown computational definition/);
  assert.throws(() => kernel.checkProof(compute(v("x"), v("x"), [])), /requires closed terms/);
  assert.equal(formulaEquals(kernel.checkProof(compute(app("zero"), app("zero"), [])), eq(app("zero"), app("zero"))), true);
});

test("huge ground arithmetic uses BigInt with constant-size certificates", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `${arithmetic}\n
theorem compact.huge
  shows 7000000000 * 1000000000 = 7000000000000000000
proof
  compute
`);
  const theorem = exportTheorem(kernel, "compact.huge");
  const proof = kernel.theoremProofs.get("compact.huge")!;
  assert.equal(proof.rule, "compute");
  assert.equal(theorem.proof.nodes.length, 1);
  assert.deepEqual(theorem.dependencies.definitions, ["plus.equation", "times.equation"]);

  const program = compileProofMachine(theorem);
  assert.equal(program.code.length, 1);
  assert.ok(program.terms.length <= 4, `unexpected term arena size ${program.terms.length}`);
  assert.ok(encodeProofMachineBinary(program).byteLength < 512);

  const execution = evaluateNative(kernel, app("times", nat("7000000000"), nat("1000000000")));
  assert.equal(execution.value, 7_000_000_000_000_000_000n);
  assert.ok(execution.stats.calls < 10, `unexpected native call count ${execution.stats.calls}`);
});

test("ground quotient rational equality uses the proved criterion with exact BigInt arithmetic", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [fileURLToPath(new URL("../lib/Grace/Cumulus/Rat/Computable.g17", import.meta.url))],
    [fileURLToPath(new URL("../lib", import.meta.url))]);
  const className = "Grace.Cumulus.Rat.Operations.rationalClass";
  const left = app(className, nat("1000000000000000000000000000000"), nat(0), nat(3));
  const right = app(className, nat("2000000000000000000000000000000"), nat(0), nat(6));
  const accepted = rationalClassCompute(left, right);
  assert.equal(formulaEquals(kernel.checkProof(accepted), eq(left, right)), true);
  const exported = exportTheorem(kernel,
    "Grace.Cumulus.Rat.Computable.RationalCellOps.rationalClass.large_ground");
  assert.equal(exported.proof.nodes.length, 1);
  assert.equal(compileProofMachine(exported).code.length, 1);
  assert.throws(() => kernel.checkProof(rationalClassCompute(left,
    app(className, nat("2000000000000000000000000000001"), nat(0), nat(6)))),
  /different normal forms/);
  assert.throws(() => kernel.checkProof(rationalClassCompute(left,
    app(className, nat(0), nat(0), nat(0)))), /positive denominators/);
  assert.throws(() => kernel.checkProof(rationalClassCompute(left,
    app(className, v("unbound"), nat(0), nat(6)))), /ground classes/);
  kernel.theorems.delete(`${className}.eq`);
  assert.throws(() => kernel.checkProof(rationalClassCompute(left, right)), /proved quotient equality criterion/);
});

test("ground computation normalizes general definitions and constructor values", () => {
  const kernel = createZfgKernel();
  const source = `
def diagonal (x : Set) : Set := pair(x, x)

define stack (n : Nat) -> Set
  | zero => empty
  | succ(k) => pair(empty, stack(k))

theorem diagonal.ground
  shows diagonal(empty) = pair(empty, empty)
proof
  compute

theorem stack.three
  shows stack(3) = pair(empty, pair(empty, pair(empty, empty)))
proof
  compute
`;
  elaborateModule(kernel, source);
  for (const name of ["diagonal.ground", "stack.three"]) {
    const statement = kernel.theorems.get(name)!;
    assert.equal(formulaEquals(kernel.checkProof(kernel.theoremProofs.get(name)!), statement), true);
    assert.equal(exportTheorem(kernel, name).proof.nodes.length, 1);
  }
  const result = evaluateNative(kernel, app("stack", nat(3)));
  const expected = app("pair", app("empty"),
    app("pair", app("empty"), app("pair", app("empty"), app("empty"))));
  assert.equal(termEquals(nativeValueToTerm(result.value), expected), true);
  assert.deepEqual(result.definitions, ["stack"]);
});

test("native specialization rejects near-miss arithmetic equations", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
define plus (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(plus(x, y))

-- This resembles multiplication, but adds succ(y) at each step.
define shiftedProduct (x y : Nat) -> Nat
  | zero, y => zero
  | succ(x), y => plus(succ(y), shiftedProduct(x, y))

theorem shiftedProduct.ground
  shows shiftedProduct(3, 5) = 18
proof
  compute
`);
  const execution = evaluateNative(kernel, app("shiftedProduct", nat(3), nat(5)));
  assert.equal(execution.value, 18n);
  assert.ok(execution.stats.reductions > 1, "near-miss was incorrectly replaced by native multiplication");
  assert.equal(formulaEquals(
    kernel.checkProof(kernel.theoremProofs.get("shiftedProduct.ground")!),
    kernel.theorems.get("shiftedProduct.ground")!,
  ), true);
});
