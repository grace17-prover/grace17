// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entry 30, the ballot problem: with a votes for A and b < a votes
// for B, the orderings of the ballots along which A stays strictly ahead
// throughout the count number (a − b)/(a + b) of all orderings. The
// counting form (a + b) · N = (a − b) · (a + b choose a), the additive form
// it comes from, the count of all orderings, the sets themselves, and the
// probability form on the uniform space of all orderings are restated in a
// workbench file as they are meant to be read, closed by the library
// theorems, and their printed forms are pinned. The counting module is then
// audited admission-free in ZF, and the probability module admission-free
// without choice.

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { createZfKernel, createZfgKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const header = "module Top100Ballot\nimport Grace.Cumulus.Combinatorics.BallotProbability\n\n";

function check(body: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Ballot.g17", source: header + body }], "ZFG",
    ["Top100Ballot.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 1200));
  assert.equal(result.sorries.length, 0);
  for (const theorem of result.theorems) assert.equal(theorem.sorries.length, 0, theorem.name);
  return new Map(result.theorems.map(item => [item.name.replace("Top100Ballot.", ""), item.statement]));
}

test("ballot problem, counting form: (a + b) · N = (a − b) · (a + b choose a) when b < a", () => {
  const statements = check(`theorem ballotCount (a b : Nat)
  requires lead : b < a
  shows (a + b) * cardinality(ballotSequences(a, b)) =
    (a - b) * ((a + b) choose a)
proof
  exact ballot.count with lead

theorem ballotAdditive (a b : Nat)
  requires le : b ≤ a
  shows cardinality(ballotSequences(a + 1, b)) + ((a + b) choose (a + 1)) =
    (a + b) choose a
proof
  exact ballotSequences.count_succ with le

theorem orderingsCount (a b : Nat)
  shows cardinality(orderings(a, b)) = (a + b) choose a
proof
  exact orderings.count at a, b
`);
  assert.equal(statements.get("ballotCount"),
    "∀ a b : ℕ, b < a → (a + b) * cardinality(ballotSequences(a, b)) = (a - b) * ((a + b) choose a)");
  assert.equal(statements.get("ballotAdditive"),
    "∀ a b : ℕ, b ≤ a → cardinality(ballotSequences(a + 1, b)) + ((a + b) choose (a + 1)) = (a + b) choose a");
  assert.equal(statements.get("orderingsCount"), "∀ a b : ℕ, cardinality(orderings(a, b)) = (a + b) choose a");
});

test("ballot problem: the sequences are the lists over 2 of length a + b with a zeros whose nonempty prefixes hold more zeros than ones", () => {
  const statements = check(`theorem ballotMembership (a b : Nat) (xs : Set)
  shows xs ∈ ballotSequences(a, b) ↔
    xs ∈ ballots(a + b) ∧ zeroVotes(xs) = a ∧ AlwaysAhead(xs)
proof
  exact ballotSequences.membership at a, b, xs

theorem ballotsMembership (n : Nat) (xs : Set)
  shows xs ∈ ballots(n) ↔ List(2, xs) ∧ length{2}(xs) = n
proof
  exact ballots.membership at n, xs

theorem alwaysAhead (xs : Set)
  shows AlwaysAhead(xs) ↔
    ∀ ys, List(2, ys) → ListPrefix(2, ys, xs) → ys ≠ [] → oneVotes(ys) < zeroVotes(ys)
proof
  constructor
  . intro ahead
    unfold AlwaysAhead at ahead
    exact ahead
  . intro ahead
    unfold AlwaysAhead
    exact ahead
`);
  assert.equal(statements.get("ballotMembership"),
    "∀ a b : ℕ, ∀ xs, xs ∈ ballotSequences(a, b) ↔ xs ∈ ballots(a + b) ∧ zeroVotes(xs) = a ∧ AlwaysAhead(xs)");
  assert.equal(statements.get("ballotsMembership"),
    "∀ n : ℕ, ∀ xs, xs ∈ ballots(n) ↔ List(2, xs) ∧ length(2, xs) = n");
  assert.equal(statements.get("alwaysAhead"),
    "∀ xs, AlwaysAhead(xs) ↔ ∀ ys, List(2, ys) → ListPrefix(2, ys, xs) → ys ≠ [] → oneVotes(ys) < zeroVotes(ys)");
});

test("ballot problem, probability form: A stays ahead with probability (a − b)/(a + b)", () => {
  const statements = check(`theorem ballotProbability (a b : Nat)
  requires lead : b < a
  shows prob(uniformWeight(orderings(a, b)), ballotSequences(a, b)) =
    (realNat(a - b):R) / (realNat(a + b):R)
proof
  exact ballot.probability with lead
`);
  assert.equal(statements.get("ballotProbability"),
    "∀ a b : ℕ, b < a → prob(uniformWeight(orderings(a, b)), ballotSequences(a, b)) = realNat(a - b) / realNat(a + b)");
});

test("the ballot theorem needs the strict lead b < a", () => {
  assert.throws(() => check(`theorem tie (a b : Nat)
  requires le : b ≤ a
  shows (a + b) * cardinality(ballotSequences(a, b)) =
    (a - b) * ((a + b) choose a)
proof
  exact ballot.count with le
`));
});

test("the ballot counting module is admission-free ZF", t => {
  const kernel = createZfKernel();
  const file = "lib/Grace/Cumulus/Combinatorics/Ballot.g17";
  const modules = loadModuleSourceGraph(kernel, [{ file, source: readFileSync(file, "utf8") }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name => /^Grace\.Cumulus\.Combinatorics\.Ballot\./.test(name));
  for (const expected of ["ballot.count", "ballotSequences.count_succ", "ballotSequences.membership",
    "ballots.membership", "leadSequences.closed_form", "orderings.count"]) {
    assert.ok(names.some(name => name.endsWith(`.${expected}`)), expected);
  }
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited`);
});

test("the ballot probability module is admission-free and its proofs use no choice", t => {
  const kernel = createZfgKernel();
  const file = "lib/Grace/Cumulus/Combinatorics/BallotProbability.g17";
  const modules = loadModuleSourceGraph(kernel, [{ file, source: readFileSync(file, "utf8") }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Combinatorics\.BallotProbability\./.test(name));
  assert.ok(names.some(name => name.endsWith(".ballot.probability")), "ballot.probability");
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited`);
});
