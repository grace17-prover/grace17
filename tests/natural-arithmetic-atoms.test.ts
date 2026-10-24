// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The natural-number arithmetic tactics on opaque atoms: a term such as
// count(X) or cardinality(A) is an admissible natural atom for arith,
// linarith, ring and ring_nf whenever Nat(t) or t ∈ ℕ is provable from the
// local facts or a library typing rule; succ(t) is read as t + 1 in every
// natural normal form; a disequality is refuted directly, and an equation
// whose side cannot be typed still substitutes into the comparisons; the
// sort guard of a rewrite rule is discharged by the same typing solver.

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
    files: [{ name: "NaturalArithmeticAtoms.g17", source }],
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

// count(X) is a defined term the arithmetic tactics never unfold: an
// opaque atom whose naturality is known only from the context.
const opaque = `module NaturalArithmeticAtoms
import Grace.Cumulus.Nat.Order

def count (X : Set) : Set := X
`;

const cardinal = `module NaturalArithmeticAtoms
import Grace.Cumulus.Cardinal.Counting
import Grace.Cumulus.Cardinal.Pigeonhole
import Grace.Cumulus.Nat.Order
`;

test("arith, linarith, ring and ring_nf type opaque atoms from local Nat facts", () => {
  check(opaque + `
theorem commuteArith (X Y : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(Y))
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  arith

theorem commuteLinarith (X Y : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(Y))
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  linarith

theorem commuteRing (X Y : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(Y))
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  ring

theorem doubleRingNf (X Y : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(Y))
  shows (count(X) + count(Y)) * 2 = 2 * count(Y) + 2 * count(X)
proof
  rcases typed with ⟨hx, hy⟩
  ring_nf

theorem boundArith (X Y : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(Y))
  requires le : count(X) ≤ count(Y)
  shows count(X) ≤ count(Y) + 1
proof
  rcases typed with ⟨hx, hy⟩
  arith
`);
});

test("membership in ℕ types an opaque atom as a local fact", () => {
  check(opaque + `
theorem commuteArith (X Y : Set)
  requires typed : count(X) ∈ ℕ ∧ count(Y) ∈ ℕ
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  arith

theorem commuteRing (X Y : Set)
  requires typed : count(X) ∈ ℕ ∧ count(Y) ∈ ℕ
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  ring

theorem commuteLinarith (X Y : Set)
  requires typed : count(X) ∈ ℕ ∧ count(Y) ∈ ℕ
  shows count(X) + count(Y) = count(Y) + count(X)
proof
  rcases typed with ⟨hx, hy⟩
  linarith
`);
});

test("succ(t) is t + 1 for arith, linarith and ring on naturals", () => {
  check(opaque + `
theorem succArith (k : Nat)
  shows succ(k) + 1 = succ(succ(k))
proof
  arith

theorem succLinarith (k : Nat)
  shows succ(k) + 1 = succ(succ(k))
proof
  linarith

theorem succRing (k : Nat)
  shows succ(k) + 1 = succ(succ(k))
proof
  ring

theorem succOpaque (X : Set)
  requires typed : Nat(count(X)) ∧ Nat(count(X))
  shows succ(count(X)) + 1 = succ(succ(count(X)))
proof
  rcases typed with ⟨hx, _⟩
  arith

theorem succBound (k : Nat)
  requires h : k ≤ 3
  shows succ(k) ≤ 4
proof
  arith
`);
});

test("arith and linarith refute a disequality between naturals directly", () => {
  check(opaque + `
theorem notOneArith (k : Nat, X : Set)
  requires h1 : k ≤ count(X)
  requires h2 : 2 ≤ k
  shows count(X) ≠ 1
proof
  arith

theorem notOneLinarith (k : Nat, X : Set)
  requires h1 : k ≤ count(X)
  requires h2 : 2 ≤ k
  shows count(X) ≠ 1
proof
  linarith

theorem notOneTyped (k : Nat, X : Set)
  requires typed : Nat(count(X)) ∧ k ≤ count(X)
  requires h2 : 2 ≤ k
  shows count(X) ≠ 1
proof
  rcases typed with ⟨hx, h1⟩
  linarith

theorem notOneStrict (k : Nat, X : Set)
  requires h1 : k < count(X)
  requires h2 : 1 ≤ k
  shows count(X) ≠ 1
proof
  arith

theorem bottomLinarith (a b : Nat)
  requires h1 : a < b
  requires h2 : b < a
  shows ⊥
proof
  linarith
`);
});

test("a rewrite rule's Nat guard is discharged from local typing facts", () => {
  check(opaque + `
theorem unitAtNat (X : Set)
  requires typed : Nat(count(X)) ∧ add(count(X), 0) = 3
  shows count(X) = 3
proof
  rcases typed with ⟨hx, h⟩
  rw add.right_unit at h
  exact h

theorem unitAtMember (X : Set)
  requires typed : count(X) ∈ ℕ ∧ add(count(X), 0) = 3
  shows count(X) = 3
proof
  rcases typed with ⟨hx, h⟩
  rw add.right_unit at h
  exact h

theorem unitGoal (X : Set)
  requires typed : Nat(count(X)) ∧ count(X) = 3
  shows add(count(X), 0) = 3
proof
  rcases typed with ⟨hx, h⟩
  rw add.right_unit
  exact h
`);
});

test("library typing rules admit cardinalities as natural atoms", () => {
  check(cardinal + `
theorem insertCount (A a : Set)
  requires finite : Finite(A)
  requires fresh : ¬(a ∈ A)
  shows cardinality(insert(a, A)) = cardinality(A) + 1
proof
  have step := cardinality.insert with finite, fresh
  arith

theorem removeCount (A a : Set)
  requires finite : Finite(A)
  requires member : a ∈ A
  shows cardinality(A ∖ {a}) + 1 = cardinality(A)
proof
  have step := cardinality.remove with finite, member
  have subset := difference.subset_left at A, {a}
  have smaller := Finite.subset with finite, subset
  linarith

theorem commuteCardinal (A B : Set)
  requires finite : Finite(A) ∧ Finite(B)
  shows cardinality(A) + cardinality(B) = cardinality(B) + cardinality(A)
proof
  rcases finite with ⟨hA, hB⟩
  ring

theorem unitAtCardinal (A : Set)
  requires finite : Finite(A) ∧ add(cardinality(A), 0) = 3
  shows cardinality(A) = 3
proof
  rcases finite with ⟨hA, h⟩
  rw add.right_unit at h
  exact h
`);
});
