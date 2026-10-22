// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createZfKernel, createZfgKernel, loadModuleSourceGraph, auditTheoremAxioms} from '../src/index.ts';
const sequential = readFileSync('examples/ComplexSequentialContinuity.g17', 'utf8');
const extreme = readFileSync('examples/ComplexPolynomialExtremeValue.g17', 'utf8');
function load(source: string, choice = false) {
  const kernel = choice ? createZfgKernel() : createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{file: 'Example.g17', source}], ['lib']);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}
test('the epsilon/delta to sequence bridge is hereditary ZF', t => {
  const kernel = load(sequential);
  const names = [...kernel.theorems.keys()].filter(n =>
    n.startsWith('Grace.Cumulus.Complex.SequentialContinuity.') || n.startsWith('ComplexSequentialContinuityExample.'));
  assert.equal(names.length, 14);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} ZF theorem entries audited`);
});
test('minimum attainment is admission-free and explicitly records Global Choice', t => {
  const kernel = load(extreme, true);
  const names = [...kernel.theorems.keys()].filter(n =>
    n.startsWith('Grace.Cumulus.Complex.ExtremeValue.') || n.startsWith('ComplexPolynomialExtremeValueExample.'));
  assert.equal(names.length, 18);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry/i.test(a)), [], name);
  }
  for (const short of ['disk_minimum', 'global_minimum', 'root_of_descent']) {
    const name = `Grace.Cumulus.Complex.ExtremeValue.complexPolynomial.${short}`;
    assert.ok(auditTheoremAxioms(kernel, name).hereditary.includes('set.globalChoice'), name);
  }
  t.diagnostic(`${names.length} extreme-value theorem entries audited`);
});
for (const premise of ['continuous', 'converges']) {
  test(`sequential continuity needs ${premise}`, () => {
    const changed = sequential.replace(new RegExp(`^  requires ${premise} :.*\\n`, 'm'), '');
    assert.notEqual(changed, sequential);
    assert.throws(() => load(changed), /premise|cannot|missing|match|unsolved/i);
  });
}
for (const premise of ['nonnegative', 'descent']) {
  test(`the extreme-value client needs ${premise}`, () => {
    const changed = extreme.replace(new RegExp(`^  requires ${premise} :.*\\n`, 'm'), '');
    assert.notEqual(changed, extreme);
    assert.throws(() => load(changed, true), /premise|cannot|missing|match|unsolved/i);
  });
}
