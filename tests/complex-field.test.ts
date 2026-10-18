// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/ComplexField.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "ComplexField.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("the concrete complex operations, ring, and inverses are admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Complex.") || name.startsWith("ComplexField."));
  assert.ok(names.length >= 40, `${names.length} theorem entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited, including concrete graph definitions`);
});

test("the explicit inverse requires a nonzero complex number", () => {
  const changed = source.replace(/^  requires nonzero :.*\n/m, "");
  assert.notEqual(changed, source);
  assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
});

test("the coordinate formula requires real coordinates", () => {
  const changed = source.replace("inverse (a b : Real)", "inverse (a b : Set)");
  assert.notEqual(changed, source);
  assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
});

test("the imaginary unit square cannot be changed to positive one", () => {
  const changed = source.replace("= C[-1]", "= C[1]");
  assert.notEqual(changed, source);
  assert.throws(() => load(changed), /goal remains.*realNeg.*realOne/i);
});
