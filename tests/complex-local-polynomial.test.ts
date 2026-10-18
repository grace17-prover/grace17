// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createZfKernel, loadModuleSourceGraph, auditTheoremAxioms} from '../src/index.ts';
const source = readFileSync('examples/ComplexLocalPolynomial.g17', 'utf8');
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{file: 'Example.g17', source: text}], ['lib']);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}
test('local factorization and root isolation are hereditary ZF', t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n =>
    n.startsWith('Grace.Cumulus.Algebra.Polynomial.HornerVanishing.') ||
    n.startsWith('Grace.Cumulus.Complex.LocalPolynomial.') ||
    n.startsWith('ComplexLocalPolynomialExample.'));
  assert.equal(names.length, 7);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited without Choice or admissions`);
});
for (const premise of ['center', 'root']) {
  test(`local polynomial client needs ${premise}`, () => {
    const changed = source.replace(new RegExp(`^  requires ${premise} :.*\n`, 'm'), '');
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /premise|cannot|missing|match|unsolved/i);
  });
}
