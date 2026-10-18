// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module ParityNormalization\nimport Grace.Cumulus.Nat\n";
const bounds = `
theorem upper (n k : Nat)
  requires bound : add(k, k) ≤ succ(add(n, n))
  shows k ≤ n
proof
  arith

theorem lower (n k : Nat)
  requires bound : succ(add(n, n)) ≤ add(k, k)
  shows succ(n) ≤ k
proof
  arith

theorem symbolic_half (n k : Nat)
  requires equality : succ(add(n, n)) = add(k, k)
  shows succ(n) ≤ k
proof
  arith

theorem nested_successors (n k : Nat)
  requires bound : add(succ(succ(n)), 0) ≤ k
  shows add(n, 2) ≤ k
proof
  arith

theorem zero_coefficient (n k m : Nat)
  requires bound : add(mul(0, n), k) ≤ m
  shows k ≤ m
proof
  arith

theorem several_zeros (n k : Nat)
  requires bound : add(add(0, n), add(k, 0)) ≤ n
  shows k ≤ 0
proof
  arith
`;

test("natural arithmetic reconstructs zero, successor and integer-rounding certificates", () => {
  assert.equal(checkWorkbenchFiles([{ name: "ParityNormalization.g17", source: header + bounds }]).ok, true);
});

test("integer rounding still rejects false bounds and missing premises", () => {
  for (const source of [
    `theorem false_lower (n k : Nat)
  requires bound : succ(add(n, n)) ≤ add(k, k)
  shows add(n, 2) ≤ k
proof
  arith`,
    `theorem false_upper (n k : Nat)
  requires bound : add(k, k) ≤ add(add(n, n), 2)
  shows k ≤ n
proof
  arith`,
    `theorem missing (n k : Nat)
  shows succ(n) ≤ k
proof
  arith`,
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "ParityNormalization.g17", source: header + source }]));
});

test("general parity survives cold and edited checks", () => {
  const file = { name: "Nat/Parity.g17", source: readFileSync("lib/Grace/Cumulus/Nat/Parity.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  file.source += "\n-- parity warm edit\n";
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
});

test("odd iff not even requires naturalness", () => {
  const source = header + `theorem guarded (n : Set)
  requires natural : Nat(n)
  shows Odd(n) ↔ ¬Even(n)
proof
  exact Odd.iff_not_even at n with *
`;
  assert.equal(checkWorkbenchFiles([{ name: "ParityNormalization.g17", source }]).ok, true);
  assert.throws(() => checkWorkbenchFiles([{ name: "ParityNormalization.g17", source: source.replace("  requires natural : Nat(n)\n", "") }]), /with \* cannot find evidence/);
});
