// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createZfKernel, createZfgKernel, loadModuleSourceGraph, auditTheoremAxioms} from '../src/index.ts';
const source = readFileSync('examples/ComplexFundamentalTheorem.g17', 'utf8');
test('FTA, square roots and concrete Nullstellensatz have no inherited admissions', t => {
  const kernel = createZfgKernel();
  const modules = loadModuleSourceGraph(kernel, [{file:'Example.g17', source}], ['lib']);
  assert.equal(modules.flatMap(m=>m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(n=>
    /^Grace.Cumulus.Complex.(MinimumDirection|SequenceAlgebra|PolynomialStationarity|FTAReduction|SquareDirections|QuadraticRoots|PowerArithmetic|OddDirections|PowerDirections|FundamentalTheorem|Nullstellensatz)\./.test(n) || n.startsWith('ComplexFundamentalTheoremExample.'));
  assert.ok(names.length >= 50);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a=>/sorry/i.test(a)), [], name);
  }
  for (const name of [
    'Grace.Cumulus.Complex.FundamentalTheorem.complexes.fundamental_theorem_of_algebra',
    'Grace.Cumulus.Complex.QuadraticRoots.complex.square_root',
    'Grace.Cumulus.Complex.Nullstellensatz.complexes.weak_nullstellensatz',
    'Grace.Cumulus.Complex.Nullstellensatz.complexes.unsatisfiable_iff_certificate',
  ]) assert.ok(auditTheoremAxioms(kernel, name).hereditary.includes('set.globalChoice'), name);
  const quadratic = auditTheoremAxioms(kernel, 'Grace.Cumulus.Complex.QuadraticRoots.complex.square_root');
  assert.equal(quadratic.complete, true);
  t.diagnostic(`${names.length} new theorem entries audited without admissions; Global Choice is explicit`);
});
test('the ordinary Complex entrypoint remains ZF and the direction algebra is choice-free', t => {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{file:'ZF.g17',source:'module ZF\nimport Grace.Cumulus.Complex\n'}], ['lib']);
  assert.equal(modules.flatMap(m=>m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(n=>
    /^Grace.Cumulus.Complex.(MinimumDirection|SequenceAlgebra|PolynomialStationarity|SquareDirections|PowerArithmetic|OddDirections)\./.test(n));
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a=>/sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} ZF entries audited without Choice`);
});
test('FTA rejects a client with the nonconstant premise omitted', () => {
  const changed = source.replace('  requires nonconstant : cs ≠ []\n', '');
  assert.notEqual(changed, source);
  const kernel = createZfgKernel();
  assert.throws(()=>loadModuleSourceGraph(kernel, [{file:'Example.g17',source:changed}], ['lib']), /premise|cannot|missing|match|unsolved/i);
});
