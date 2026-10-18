// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from '../src/index.ts';
const source = readFileSync('examples/ComplexPolynomialMinimum.g17', 'utf8');
function load(source: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{file:'Example.g17', source}], ['lib']);
  assert.equal(modules.flatMap(m => m.sorries).length, 0); return kernel;
}
test('complex estimates, translation and conditional minimum reduction are checked in ZF', t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n => /ComplexPolynomialMinimumExample|Complex.Norm|Complex.PolynomialMinimum|Polynomial.HornerTranslation/.test(n));
  assert.ok(names.length >= 25);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true); assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), []);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});
for (const premise of ['minimum', 'descent', 'direction']) test(`the ${premise} premise cannot be omitted`, () => {
  const changed = source.replace(new RegExp(`^  requires ${premise} :.*\\n`, 'm'), '');
  assert.notEqual(changed, source);
  assert.throws(() => load(changed), /cannot|does not match|unknown|missing|unsolved|premise/i);
});
