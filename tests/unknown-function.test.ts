// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A misspelt function name in a term is an error at the line that writes
// it, with the nearest declared name suggested, rather than an unknown
// symbol that survives until the goal fails to close.

import assert from "node:assert/strict";
import test from "node:test";
import { checkWorkbenchFiles } from "../src/workbench.ts";

test("an application of an undeclared function is an error with a suggestion", () => {
  const source = `module UnknownFunction
import Grace.Cumulus.Set.Function

theorem typo (A : Set)
  shows ∃ f, FunctionBetween(f, A, A)
proof
  witness indentity(A)
  exact identity.function at A
`;
  assert.throws(
    () => checkWorkbenchFiles([{ name: "UnknownFunction.g17", source }]),
    /unknown function indentity; did you mean identity\?/,
  );
});
