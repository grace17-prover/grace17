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

// `cc [facts]` chains the listed facts alone, with the opened guard facts.
test("a fact left out of the list no longer closes the goal it would have closed", () => {
  load("Listed", `
theorem chain (x y z : Set)
  requires xy : x = y
  requires yz : y = z
  shows pair(x, x) = pair(z, z)
proof
  cc [xy, yz]
`);
  const message = failure("Restricted", `
theorem chain (x y z : Set)
  requires xy : x = y
  requires yz : y = z
  shows pair(x, x) = pair(z, z)
proof
  cc [xy]
`);
  assert.match(message, /line 8/);
});

test("a theorem instance in the list joins the equalities, which bare cc cannot use", () => {
  const source = (step: string) => `
def twice (x : Set) : Set := pair(x, x)

theorem double (a : Set)
  shows twice(a) = pair(a, a)
proof
  unfold twice
  rfl

theorem through (x y : Set)
  requires xy : x = y
  shows twice(x) = pair(y, y)
proof
  ${step}
`;
  load("Instance", source("cc [xy, double at x]"));
  load("Parenthesized", source("cc [xy, (double at x)]"));
  assert.match(failure("Bare", source("cc")), /line 15/);
});

test("a listed name that is neither a local fact nor a theorem is an error", () => {
  const message = failure("Unknown", `
theorem chain (x y : Set)
  requires xy : x = y
  shows pair(x, x) = pair(y, y)
proof
  cc [xy, nothing]
`);
  assert.match(message, /line 7: cc: nothing is neither a local fact nor a theorem/);
});
