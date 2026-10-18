// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
test('the distribution worker searches bundled and newly added libraries without kernel checking', async () => {
  const oldSelf = globalThis.self;
  let receive: (event: any)=>void; const replies: any[] = [];
  globalThis.self = {addEventListener: (_type, callback)=>{receive=callback;}, postMessage: data=>replies.push(data)} as any;
  try {
    await import('../workbench/library-search-worker.js');
    receive!({data:{id:1,query:'name:strict_descent module:Complex'}});
    assert.equal(replies[0].result.total, 1);
    assert.ok(replies[0].result.indexed > 4900);
    receive!({data:{id:2,query:'name:uniqueUserResult',files:[{name:'User.g17',source:'module User\nnamespace User\ntheorem uniqueUserResult\n  shows x = x\nproof\n  rfl\nend User'}]}});
    assert.equal(replies[1].result.results[0].file, 'User.g17');
    receive!({data:{id:3,query:'name:uniqueUserResult',files:[]}});
    assert.equal(replies[2].result.total, 0);
    receive!({data:{id:4,query:'bad:query'}});
    assert.match(replies[3].error, /Unknown filter/);
    receive!({data:{id:5,query:'name:difference_bound_on_disk'}});
    assert.equal(replies[4].result.total, 1);
    assert.match(replies[4].result.results[0].file, /Complex\/PolynomialBounds\.g17$/);
    receive!({data:{id:6,query:'name:complexPolynomial.continuous'}});
    assert.equal(replies[5].result.total, 2);
    assert.ok(replies[5].result.results.every(r=>r.file.endsWith('Complex/Continuity.g17')));
    receive!({data:{id:7,query:'name:grows_at_infinity module:Complex'}});
    assert.equal(replies[6].result.total, 1);
    assert.ok(replies[6].result.results[0].file.endsWith('Complex/PolynomialGrowth.g17'));
    receive!({data:{id:8,query:'name:closedComplexDisk.sequentially_compact'}});
    assert.equal(replies[7].result.total, 1);
    assert.ok(replies[7].result.results[0].file.endsWith('Complex/Compactness.g17'));
    receive!({data:{id:9,query:'name:complexPolynomial.global_minimum'}});
    assert.equal(replies[8].result.total, 1);
    assert.ok(replies[8].result.results[0].file.endsWith('Complex/ExtremeValue.g17'));
    receive!({data:{id:10,query:'name:ComplexContinuousAt.converges'}});
    assert.equal(replies[9].result.total, 1);
    assert.ok(replies[9].result.results[0].file.endsWith('Complex/SequentialContinuity.g17'));
    receive!({data:{id:11,query:'name:complexPolynomial.local_normal_form'}});
    assert.equal(replies[10].result.total, 1);
    assert.ok(replies[10].result.results[0].file.endsWith('Complex/LocalPolynomial.g17'));
    receive!({data:{id:12,query:'name:complexPolynomial.ray_normal_form'}});
    assert.equal(replies[11].result.total, 1);
    assert.ok(replies[11].result.results[0].file.endsWith('Complex/Descent.g17'));
    receive!({data:{id:13,query:'name:complexes.fundamental_theorem_of_algebra'}});
    assert.equal(replies[12].result.total, 3);
    assert.ok(replies[12].result.results[0].file.endsWith('Complex/FundamentalTheorem.g17'));
    assert.ok(replies[12].result.results.slice(1).every(r=>r.file.endsWith('Complex/FundamentalTheoremGeneral.g17')));
    receive!({data:{id:14,query:'name:complexes.weak_nullstellensatz'}});
    assert.equal(replies[13].result.total, 1);
  } finally { globalThis.self = oldSelf; }
});
