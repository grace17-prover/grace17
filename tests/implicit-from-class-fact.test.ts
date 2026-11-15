// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

function load(name: string, source: string): void {
  loadModuleSourceGraph(createZfKernel(), [{ file: `${name}.g17`, source: `module ${name}\n${source}` }], ["lib"]);
}

function failure(name: string, source: string): string {
  try {
    load(name, source);
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
  throw new Error(`${name} was expected to fail`);
}

test("an implicit is read off a class fact in scope about the argument", () => {
  load("ImplicitFact", `import Grace.Core.Data

theorem append.of_fact (C : Set)
  requires given : ∃ xs, List(C, xs)
  shows ∃ zs, List(C, zs)
proof
  obtain ⟨xs, xsList⟩ := given
  have appended : List(C, append(xs, xs)) by typecheck
  exact ⟨append(xs, xs), appended⟩
`);
});

test("facts that disagree fix nothing, and no fact keeps the report", () => {
  const disagree = failure("ImplicitDisagree", `import Grace.Core.Data

theorem append.ambiguous (C D : Set)
  requires given : ∃ xs, List(C, xs) ∧ List(D, xs)
  shows ∃ zs, List(C, zs)
proof
  obtain ⟨xs, xsList, xsOther⟩ := given
  have appended : List(C, append(xs, xs)) by typecheck
  exact ⟨append(xs, xs), appended⟩
`);
  assert.match(disagree, /cannot infer implicit argument A for append; use append\{A := \.\.\.\}/u);
  const none = failure("ImplicitNone", `import Grace.Core.Data

theorem append.untyped (C : Set)
  requires given : ∃ xs, xs = xs
  shows ∃ zs, zs = zs
proof
  obtain ⟨xs, same⟩ := given
  have appended : append(xs, xs) = append(xs, xs) by rfl
  exact ⟨xs, same⟩
`);
  assert.match(none, /cannot infer implicit argument A for append/u);
});
