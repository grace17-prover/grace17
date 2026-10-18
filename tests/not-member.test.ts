// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// `x ∉ A` is read as `¬(x ∈ A)` and printed back the same way.
test("the not-member symbol abbreviates negated membership", () => {
  const source = `module NotMember
import Grace.Cumulus.Set.Core

theorem empty_has_nothing (x : Set)
  shows x ∉ ∅
proof
  intro member
  exact set.empty at x with member

theorem unfolded (x A : Set)
  requires outside : x ∉ A
  shows ¬(x ∈ A)
proof
  exact outside
`;
  const result = checkWorkbenchFiles([{ name: "NotMember.g17", source }], "ZF", ["NotMember.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
  const statements = result.theorems.map(theorem => theorem.statement);
  assert.ok(statements.some(statement => statement.includes("∀ x, x ∉ ∅")), statements.join("\n"));
  assert.ok(statements.some(statement => statement.includes("x ∉ A → x ∉ A")), statements.join("\n"));
});
