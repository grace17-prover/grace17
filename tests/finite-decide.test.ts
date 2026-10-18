// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

function check(name: string, statement: string, proof = "decide") {
  const source = `module Decide.${name}\nimport Grace.Cumulus.Cardinal\n\ntheorem ${name}\n  shows ${statement}\nproof\n  ${proof}\n`;
  return checkWorkbenchFiles([{ name: `${name}.g17`, source }], "ZFG", [`${name}.g17`], { includeKernelDetails: false });
}

// `decide` evaluates a closed finite-set statement and certifies it with a
// generated script over the membership lemmas; every step is kernel-checked.
test("decide settles closed membership, inclusion, equality and their negations over set literals", () => {
  const statements: [string, string][] = [
    ["member", "2 ∈ {1, 2, 3}"],
    ["notMember", "4 ∉ {1, 2, 3}"],
    ["subset", "{1, 2} ⊆ {1, 2, 3}"],
    ["union", "{1, 2} ∪ {2, 3} = {1, 2, 3}"],
    ["commute", "{1, 2} = {2, 1}"],
    ["powersetMember", "{1} ∈ 𝒫({1, 2})"],
    ["emptyMember", "1 ∉ ∅"],
    ["difference", "{1, 2, 3} ∖ {2} = {1, 3}"],
    ["intersection", "{1, 2} ∩ {2, 3} = {2}"],
    ["distinct", "{1, 2} ≠ {1}"],
    ["subsetsOfPowerset", "{{1}, {2}} ⊆ 𝒫({1, 2})"],
    ["insertLiteral", "insert(0, {1, 2}) = {0, 1, 2}"],
    ["numeralMember", "2 ∈ 5"],
    ["numeralSuperset", "{0, 1} ⊆ 2"],
    ["disjoint", "{5, 6} ∩ {7} = ∅"],
    ["notSubset", "¬({1, 2} ⊆ {1})"],
    ["nested", "{{1, 2}} = {{2, 1}}"],
    ["unionMiss", "7 ∉ {1, 2, 3} ∪ {4, 5}"],
  ];
  for (const [name, statement] of statements) {
    const result = check(name, statement);
    assert.equal(result.ok, true, `${statement}: ${result.message}`);
    assert.equal(result.theorems.flatMap((theorem: { sorries?: unknown[] }) => theorem.sorries ?? []).length, 0);
  }
});

test("decide reports false statements and the edge of its fragment", () => {
  assert.throws(() => check("falseMember", "4 ∈ {1, 2, 3}"), /decide: 4 ∈ \{1, 2, 3\} is false/);
  assert.throws(() => check("falseEqual", "{1} = {2}"), /decide: .* is false/);
  assert.throws(() => check("powersetLeft", "𝒫({1}) = {∅, {1}}"), /powerset on the left/);
  assert.throws(() => check("notClosed", "∀ x, x ∈ {1} → x = 1"), /decide proves closed goals/);
});

test("decide handles a literal written with a repeated element", () => {
  const source = `module DecideRepeated
import Grace.Cumulus.Cardinal

theorem union_of_two
  shows {1, 2} ∪ {2, 3} = {1, 2, 3, 3}
proof
  decide
`;
  const result = checkWorkbenchFiles([{ name: "DecideRepeated.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 300));
});
