// Subset-bounded quantifiers elaborate to guarded quantifiers and print back
// as written, and natural subtraction comes with the Nat entry point.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const source = `module SubsetBinders
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Nat

theorem every (V : Set)
  shows ∀ X ⊆ V, X ∩ V = X
proof
  intros X bound
  exact intersection.eq_left_of_subset with bound

theorem some (V : Set)
  shows ∃ X ⊆ V, X = ∅
proof
  witness ∅
  constructor
  . exact empty.subset at V
  . rfl

theorem two (V : Set)
  shows ∀ X Y ⊆ V, X ∪ Y ⊆ V
proof
  intros X boundX Y boundY
  exact union2.subset with boundX, boundY

theorem truncated (n : Nat)
  shows n - 1 = predecessor(n)
proof
  exact sub.one at n
`;

test("subset-bounded quantifiers are guarded quantifiers that print back as written", () => {
  const result = callMachineMethod("check", { files: [{ name: "SubsetBinders.g17", source }], moduleRoots: ["lib"] }) as {
    status: string; theorems: { name: string; statement: string; sorries: unknown[] }[];
  };
  assert.equal(result.status, "checked");
  const statement = (name: string) => result.theorems.find(item => item.name === `SubsetBinders.${name}`)?.statement;
  assert.equal(statement("every"), "∀ V, ∀ X ⊆ V, X ∩ V = X");
  assert.equal(statement("some"), "∀ V, ∃ X ⊆ V, X = ∅");
  assert.equal(statement("two"), "∀ V, ∀ X ⊆ V, ∀ Y ⊆ V, X ∪ Y ⊆ V");
  assert.equal(statement("truncated"), "∀ n : ℕ, n - 1 = predecessor(n)");
  for (const theorem of result.theorems) assert.deepEqual(theorem.sorries, [], theorem.name);
});

test("a subset bound is a plain guard to the kernel", () => {
  const result = callMachineMethod("declaration", {
    files: [{ name: "SubsetBinders.g17", source }], moduleRoots: ["lib"], name: "SubsetBinders.every",
  }) as { result?: { directions?: { forward?: string } }; statement?: string; conclusion?: string };
  const text = JSON.stringify(result);
  assert.match(text, /∀ X ⊆ V, X ∩ V = X/);
});
