// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Counting arguments as they arise in combinatorics and graph theory: two
// equations meeting through succ are combined by arith, a cardinality is a
// natural atom whenever Finite(X) is in context, a bound a ≤ b types its
// right side once its left side is typed, and cc refutes a disequality goal
// by assuming the equation.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

interface CheckResult {
  status: string;
  theorems: { name: string; status: string }[];
  diagnostics: { severity: string; line: number; message: string }[];
}

function check(source: string): void {
  const result = callMachineMethod("check", {
    files: [{ name: "CountingArithmetic.g17", source }],
  }) as CheckResult;
  const errors = result.diagnostics
    .filter(item => item.severity === "error")
    .map(item => `line ${item.line}: ${item.message}`);
  const unproved = result.theorems
    .filter(item => item.status !== "proved")
    .map(item => `${item.name}: ${item.status}`);
  assert.deepEqual([...errors, ...unproved], [], errors.join("\n"));
  assert.ok(result.theorems.length > 0, "the module declares theorems");
}

const cardinal = `module CountingArithmetic
import Grace.Cumulus.Cardinal.Counting
import Grace.Cumulus.Cardinal.Pigeonhole
import Grace.Cumulus.Nat.Order
`;

test("arith combines two equations through succ by cancellation", () => {
  check(cardinal + `
theorem removeSize (F e : Set, k : Nat)
  requires finite : Finite(F)
  requires restFinite : Finite(F ∖ {e})
  requires removed : cardinality(F) = succ(cardinality(F ∖ {e}))
  requires size : cardinality(F) = succ(k)
  shows cardinality(F ∖ {e}) = k
proof
  arith

theorem removeSizeSucc (F a : Set, k : Nat)
  requires restFinite : Finite(F ∖ {a})
  requires removed : succ(k) = succ(cardinality(F ∖ {a}))
  shows cardinality(F ∖ {a}) = k
proof
  arith

theorem removeSizeUntyped (F e : Set, k : Nat)
  requires finite : Finite(F)
  requires member : e ∈ F
  requires size : cardinality(F) = succ(k)
  shows cardinality(F ∖ {e}) = k
proof
  have removed := cardinality.remove with finite, member
  arith

theorem removeSizePlusOne (F e : Set, k : Nat)
  requires finite : Finite(F)
  requires restFinite : Finite(F ∖ {e})
  requires removed : cardinality(F) = cardinality(F ∖ {e}) + 1
  requires size : cardinality(F) = succ(k)
  shows cardinality(F ∖ {e}) = k
proof
  arith

theorem commonSummand (A B C : Set)
  requires finite : Finite(A) ∧ Finite(B) ∧ Finite(C)
  requires left : cardinality(A) + cardinality(C) = 7
  requires right : cardinality(B) + cardinality(C) = 7
  shows cardinality(A) = cardinality(B)
proof
  rcases finite with ⟨hA, hB, hC⟩
  arith
`);
});

test("a cardinality is a natural atom from Finite alone", () => {
  check(cardinal + `
theorem boundFinite (A B : Set)
  requires finiteA : Finite(A)
  requires finiteB : Finite(B)
  requires le : cardinality(A) ≤ cardinality(B)
  shows cardinality(A) ≤ cardinality(B) + 1
proof
  arith

theorem sumFinite (A B : Set)
  requires finiteA : Finite(A)
  requires finiteB : Finite(B)
  shows cardinality(A) + cardinality(B) = cardinality(B) + cardinality(A)
proof
  arith

theorem chainFinite (E : Set, k m : Nat)
  requires finite : Finite(E)
  requires below : k ≤ cardinality(E)
  requires above : cardinality(E) ≤ m
  shows k ≤ m
proof
  linarith

theorem strictFinite (E : Set, k m : Nat)
  requires finite : Finite(E)
  requires below : k < cardinality(E)
  requires above : cardinality(E) ≤ m
  shows k < m
proof
  linarith
`);
});

test("a bound a ≤ b types its right side from its left", () => {
  check(cardinal + `
theorem chainOrder (E : Set, k m : Nat)
  requires below : k ≤ cardinality(E)
  requires above : cardinality(E) ≤ m
  shows k ≤ m
proof
  linarith

theorem rightOfBound (X : Set, k : Nat)
  requires below : k ≤ cardinality(X)
  shows k ≤ cardinality(X) + 1
proof
  arith

theorem rightOfBoundLinarith (X : Set, k : Nat)
  requires below : k ≤ cardinality(X)
  shows k ≤ cardinality(X) + 1
proof
  linarith

theorem rightOfStrict (X : Set, k : Nat)
  requires below : k < cardinality(X)
  shows k + 1 ≤ cardinality(X)
proof
  arith

theorem twoBounds (X Y : Set, k : Nat)
  requires first : k ≤ cardinality(X)
  requires second : cardinality(X) ≤ cardinality(Y)
  shows k ≤ cardinality(Y) + 1
proof
  linarith
`);
});

test("cc proves a disequality by assuming the equation", () => {
  check(cardinal + `
theorem loopNot (leftEnd rightEnd e v : Set)
  requires loop : leftEnd(e) = rightEnd(e)
  requires atV : leftEnd(e) ≠ v
  shows rightEnd(e) ≠ v
proof
  cc

theorem loopNotCongruence (leftEnd rightEnd e v : Set)
  requires loop : leftEnd(e) = rightEnd(e)
  requires atV : leftEnd(e) ≠ v
  shows rightEnd(e) ≠ v
proof
  congruence

theorem loopBottom (leftEnd rightEnd e v : Set)
  requires loop : leftEnd(e) = rightEnd(e)
  requires atV : leftEnd(e) ≠ v
  requires same : rightEnd(e) = v
  shows ⊥
proof
  cc

theorem predicateNot (f : Set, a b : Set)
  requires same : a = b
  requires missing : ¬(f(a) ∈ b)
  shows ¬(f(b) ∈ a)
proof
  cc
`);
});
