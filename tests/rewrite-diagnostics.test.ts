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

test("a rewrite that would match in the other orientation says so", () => {
  const message = failure("RewriteOrientation", `import Grace.Cumulus.List.TakeDrop

theorem orientation (g q q2 : Nat)
  requires h : g * q2 = q
  requires zero : g * q2 = 0
  shows q = 0
proof
  rw h
  exact zero
`);
  assert.match(message, /rewrite rule h \(g \* q2 = q\) does not match the goal q = 0; the other orientation, rw ← h, matches/u);
});

test("a rewrite whose premise is not established names the premise", () => {
  const message = failure("RewriteGuard", `import Grace.Cumulus.List.TakeDrop

theorem guard (A d ds : Set)
  requires same : listDrop{A}(0, d :: ds) = d :: ds
  shows listDrop{A}(0, d :: ds) = d :: ds
proof
  rw listDrop.zero
  rfl
`);
  assert.match(message, /rewrite rule listDrop\.zero \(listDrop\(A, 0, xs\) = xs\) matches the goal listDrop\(A, 0, d :: ds\) = d :: ds, but its premise List\(A, d :: ds\) is not established; prove it first or supply it with `with`/u);
});

test("the orientation hint is given at a fact too", () => {
  const message = failure("RewriteOrientationAt", `import Grace.Cumulus.List.TakeDrop

theorem orientation (g q q2 : Nat)
  requires h : g * q2 = q
  requires zero : q = 0
  shows g * q2 = 0
proof
  rw h at zero
  exact zero
`);
  assert.match(message, /does not match zero : q = 0; the other orientation, rw ← h at zero, matches/u);
});
