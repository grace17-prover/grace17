// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { app, termEquals, v, substituteTerm } from "../src/ast.ts";

test("bounded AST interning retains FIFO semantics through eviction and reinsertion", () => {
  const x = v("fifo_x");
  const first = app("fifo_first", x);
  for (let index = 0; index < 32767; index++) app(`fifo_${index}`, x);
  assert.equal(app("fifo_first", x), first, "a hit still reuses the current node");
  const newest = app("fifo_last", x);
  const reinserted = app("fifo_first", x);
  assert.notEqual(reinserted, first, "a hit must not change FIFO eviction order");
  assert.ok(termEquals(reinserted, first), "eviction must not change mathematical equality");
  assert.equal(app("fifo_last", x), newest);
  assert.equal(app("fifo_first", x), reinserted);
  assert.ok(Object.isFrozen(reinserted));
  assert.ok(reinserted.tag === "app" && Object.isFrozen(reinserted.args));
});

test("substitution preserves constants and observes edits between calls", () => {
  const constant = app("constant");
  assert.equal(substituteTerm(constant, "x", v("y")), constant);
  const mutable = { tag: "var" as const, name: "x" };
  const term = { tag: "app" as const, fn: "f", args: [constant, mutable] };
  assert.deepEqual(substituteTerm(term, "x", v("z")), app("f", constant, v("z")));
  mutable.name = "y";
  assert.equal(substituteTerm(term, "x", v("z")), term);
});
