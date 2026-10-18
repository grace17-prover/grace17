// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createZfKernel, loadModuleSourceGraph, auditTheoremAxioms} from '../src/index.ts';
const source = readFileSync('examples/ComplexPolynomialGrowth.g17','utf8');
function load(source: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel,[{file:'Example.g17',source}],['lib']);
  assert.equal(modules.flatMap(m=>m.sorries).length,0);
  return kernel;
}
test('growth and the conditional disk reduction are admission-free in ZF', t => {
  const kernel=load(source);
  const names=[...kernel.theorems.keys()].filter(n=>n.startsWith('Grace.Cumulus.Complex.PolynomialGrowth.') || n.startsWith('ComplexPolynomialGrowthExample.'));
  assert.equal(names.length,13);
  for(const name of names) {
    const audit=auditTheoremAxioms(kernel,name);
    assert.equal(audit.complete,true,name);
    assert.deepEqual(audit.hereditary.filter(a=>/sorry|choice/i.test(a)),[],name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});
for(const premise of ['unitBound','diskMinima']) test(`the current proof requires ${premise}`,()=>{
  const changed=source.replace(new RegExp(`^  requires ${premise} :.*\\n`,'m'),'');
  assert.notEqual(changed,source);
  assert.throws(()=>load(changed),/premise|cannot|missing|match|unsolved/i);
});
test('the constant polynomial one cannot be certified to grow at infinity',()=>{
  const changed=source.replace('complexPolynomial(c :: cs)(z)','complexPolynomial([])(z)');
  assert.notEqual(changed,source);
  assert.throws(()=>load(changed),/premise|cannot|missing|match|unsolved/i);
});
