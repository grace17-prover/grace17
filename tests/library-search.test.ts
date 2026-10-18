// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { LibrarySearchIndex, LibrarySearchWorkspace, matchesSourcePattern, parseSearchQuery, scanSearchDeclarations } from '../workbench/library-search.js';
const source = `module User.Geometry
namespace Geometry
section Points
variable (a : Set)
hypothesis point : Point(a)
-- Reflexivity of distance.
theorem distance.self (x : Set)
  requires hx : Point(x)
  shows distance(x, x) = 0
proof
  sorry
end Points
theorem other
  shows a = b
proof
  sorry
end Geometry
`;
test('declarations retain qualified names, source positions, documentation and section context', () => {
  const [first, second] = scanSearchDeclarations('User.g17', source);
  assert.equal(first.name, 'Geometry.distance.self'); assert.equal(first.line, 7);
  assert.equal(first.documentation, 'Reflexivity of distance.');
  assert.match(first.context, /Point\(a\)/); assert.equal(second.context, '');
  assert.equal(first.conclusion, 'distance(x, x) = 0'); assert.doesNotMatch(first.signature, /sorry/);
});
test('AND, exclusions, exact symbol boundaries and field filters', () => {
  const index = new LibrarySearchIndex(); index.updateFile('User.g17', source);
  assert.equal(index.search('module:Geometry kind:theorem "Reflexivity of distance"').total, 1);
  assert.equal(index.search('symbol:distance -name:other').total, 1);
  assert.equal(index.search('symbol:dist').total, 0);
  assert.equal(index.search('conclusion:"a = b"').results[0].name, 'Geometry.other');
  assert.equal(index.search('pattern:"distance(?x, ?x)"').total, 1);
});
test('balanced patterns preserve repeated bindings and reject unequal expressions', () => {
  assert.equal(matchesSourcePattern('f(g(x), g(x)) = z', 'f(?a, ?a)'), true);
  assert.equal(matchesSourcePattern('f(g(x), g(y)) = z', 'f(?a, ?a)'), false);
  assert.equal(matchesSourcePattern('f(g(x), g(y))', 'f(_, _)'), true);
  assert.equal(matchesSourcePattern('f((x), y)', 'f(?a, ?a)'), false);
  assert.throws(() => matchesSourcePattern('a = a', '?x = ?x', {remaining: 0}), /budget/);
});
test('edits and removals invalidate caches and postings', () => {
  const index = new LibrarySearchIndex(); index.updateFile('User.g17', source);
  assert.equal(index.search('distance').cached, false); assert.equal(index.search('distance').cached, true);
  assert.equal(index.updateFile('User.g17', source), false);
  index.updateFile('User.g17', source.replaceAll('distance', 'metric'));
  assert.equal(index.search('distance').total, 0); assert.equal(index.search('metric').total, 1);
  index.removeFile('User.g17'); assert.equal(index.search('').indexed, 0); assert.equal(index.postings.size, 0);
});
test('bad queries receive actionable diagnostics', () => {
  for (const text of ['wat:x', 'name:', '"unclosed']) assert.throws(() => parseSearchQuery(text));
  assert.throws(() => parseSearchQuery('x'.repeat(1025)), /1,024/);
  assert.throws(() => matchesSourcePattern('x', Array(129).fill('x').join(' ')), /128 tokens/);
});

test('workspace module overrides and deleted library files leave no stale results', () => {
  const workspace = new LibrarySearchWorkspace(new Map([['lib/Geometry.g17', source]]));
  workspace.sync([{ name: 'Geometry.g17', source: source.replaceAll('distance', 'metric') }]);
  assert.equal(workspace.index.search('distance').total, 0);
  assert.equal(workspace.index.search('metric').results[0].file, 'Geometry.g17');
  workspace.sync([{ name: 'Other.g17', source: 'module Other\ntheorem userResult\n  shows x = x\nproof\n  rfl' }]);
  assert.equal(workspace.index.search('metric').total, 0);
  assert.equal(workspace.index.search('distance').total, 1);
  assert.equal(workspace.index.search('userResult').total, 1);
  workspace.sync([]); assert.equal(workspace.index.search('userResult').total, 0);
});
