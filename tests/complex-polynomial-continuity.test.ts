// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createZfKernel, loadModuleSourceGraph, auditTheoremAxioms} from '../src/index.ts';
const source = readFileSync('examples/ComplexPolynomialContinuity.g17','utf8');
function load(source: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel,[{file:'Example.g17',source}],['lib']);
  assert.equal(modules.flatMap(m=>m.sorries).length,0);
  return kernel;
}
test('all coefficient-list polynomials are continuous in ZF with no admissions', t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n=>n.startsWith('Grace.Cumulus.Complex.Continuity.') || n.startsWith('ComplexPolynomialContinuityExample.'));
  assert.equal(names.length,13);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel,name);
    assert.equal(audit.complete,true,name);
    assert.deepEqual(audit.hereditary.filter(a=>/sorry|choice/i.test(a)),[],name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});
for (const premise of ['center','epsilon','small']) test(`the ${premise} premise cannot be omitted`, () => {
  const changed = source.replace(new RegExp(`^  requires ${premise} :.*\\n`,'m'),'');
  assert.notEqual(changed,source);
  assert.throws(()=>load(changed), /premise|cannot|missing|match|unsolved/i);
});
