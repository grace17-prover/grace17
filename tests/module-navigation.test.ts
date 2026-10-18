// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { importCandidates, indexModuleDocuments, importSymbolAt } from '../workbench/module-navigation.js';
const bundled = indexModuleDocuments([['lib/A.g17', '-- A useful mathematical module.\n-- Authors: Grant Passmore\n\nmodule A\n']]);
test('import hover and navigation work without a checked result', () => {
  const s = importSymbolAt('import A -- explanation', 7, [], bundled);
  assert.equal(s?.file, 'lib/A.g17');
  assert.match(s!.info, /useful mathematical module/);
  assert.equal(s?.document.source.split('\n')[s.line - 1].trim(), 'module A');
  for (const offset of [0, 6, 8, 12]) assert.equal(importSymbolAt('import A -- explanation', offset, [], bundled), undefined);
  assert.equal(importSymbolAt('-- import A', 10, [], bundled), undefined);
});
test('live workspace edits override bundled modules; ambiguity never guesses', () => {
  const files = [{name:'Local.g17',source:'-- Edited\nmodule A\n'}];
  assert.equal(importSymbolAt('import A',7,files,bundled)?.file,'Local.g17');
  files.push({name:'Duplicate.g17',source:'module A\n'});
  const ambiguous = importSymbolAt('import A',7,files,bundled);
  assert.equal(ambiguous?.file,undefined);
  assert.match(ambiguous!.info,/Ambiguous/);
  assert.match(importSymbolAt('import Missing',8,[],bundled)!.info,/not available/);
});
test('edited imports and user-library documents resolve against current text', () => {
 const file={name:'User.g17',source:'module A\n'};
 assert.equal(importSymbolAt('import A',7,[file],bundled)?.file,'User.g17');
 file.source='module B\n';
 assert.equal(importSymbolAt('import A',7,[file],bundled)?.file,'lib/A.g17');
 assert.equal(importSymbolAt('import B',7,[file],bundled)?.file,'User.g17');
 const docs=[{file:'user/Tools.g17',module:'Tools',source:'-- User library\nmodule Tools\n'}];
 assert.equal(importSymbolAt('import Tools',8,[],bundled,docs)?.file,'user/Tools.g17');
});

test("an import is resolved relative to the importing module, innermost first, so Cmd+click lands on the module it names", () => {
  const library = new Map([
    ["lib/Grace/Cumulus/Algebra/Group.g17", "module Grace.Cumulus.Algebra.Group\nimport Power\nimport Set.Function\n"],
    ["lib/Grace/Cumulus/Algebra/Group/Power.g17", "module Grace.Cumulus.Algebra.Group.Power\n"],
    ["lib/Grace/Cumulus/Set/Function.g17", "module Grace.Cumulus.Set.Function\n"],
    ["lib/Grace/Cumulus/Power.g17", "module Grace.Cumulus.Power\n"],
  ]);
  const index = indexModuleDocuments(library);
  const source = library.get("lib/Grace/Cumulus/Algebra/Group.g17");
  const power = importSymbolAt(source, source.indexOf("Power"), [], index, []);
  assert.equal(power.name, "Grace.Cumulus.Algebra.Group.Power");
  assert.equal(power.short, "Power");
  assert.equal(power.file, "lib/Grace/Cumulus/Algebra/Group/Power.g17");
  assert.equal(power.line, 1);
  const fn = importSymbolAt(source, source.indexOf("Set.Function"), [], index, []);
  assert.equal(fn.file, "lib/Grace/Cumulus/Set/Function.g17");
  assert.match(fn.info, /^module Grace\.Cumulus\.Set\.Function\n/u);
  assert.deepEqual(importCandidates("A.B.C", "X"), ["A.B.C.X", "A.B.X", "A.X", "X"]);
});
