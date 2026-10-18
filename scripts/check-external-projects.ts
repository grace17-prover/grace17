// Exercise independent source libraries from a working directory outside Grace17.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';

const root = fileURLToPath(new URL('../', import.meta.url));
const workspace = mkdtempSync(join(tmpdir(), 'grace17-external-'));
function run(args: string[], success = true) {
  const result = spawnSync(process.execPath, [join(root, 'bin/g17.ts'), ...args], {
    cwd: workspace, encoding: 'utf8', timeout: 120000, maxBuffer: 16 * 1024 * 1024,
  });
  if (result.error) throw result.error;
  if (success) assert.equal(result.status, 0, result.stderr || result.stdout);
  else assert.notEqual(result.status, 0, 'Expected failure');
  return result;
}
try {
  mkdirSync(join(workspace, 'library/Shared'), { recursive: true });
  mkdirSync(join(workspace, 'client'), { recursive: true });
  writeFileSync(join(workspace, 'library/Shared/Sets.g17'), `module Shared.Sets
import Grace.Cumulus.Set.Core

theorem subset_chain (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  exact Subset.transitive with *
`);
  writeFileSync(join(workspace, 'client/Main.g17'), `module Client
import Shared.Sets

theorem subset_three_steps (A B C D : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  requires third : C ⊆ D
  shows A ⊆ D
proof
  have middle : A ⊆ C := subset_chain with *
  exact subset_chain with *

`);
  const roots = ['--foundation', 'ZF', '--module-root', join(root, 'lib'), '--module-root', 'library'];
  const checked = JSON.parse(run(['check', '--json', ...roots, 'client/Main.g17']).stdout);
  assert.equal(checked.ok, true);
  assert(checked.checked.every((m: { sorries: unknown[] }) => m.sorries.length === 0));
  const audit = JSON.parse(run(['axiom-audit', '--json', ...roots, 'client/Main.g17', '--theorem', 'Client.subset_three_steps']).stdout);
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.hereditary, []);
  for (const name of ['first', 'second']) {
    run(['compile', ...roots, 'client/Main.g17', '--out', `${name}.g17m`, '--environment', `${name}.g17env`]);
  }
  for (const extension of ['g17m', 'g17env']) {
    assert.deepEqual(readFileSync(join(workspace, `first.${extension}`)), readFileSync(join(workspace, `second.${extension}`)));
  }
  const independent = spawnSync('python3', [join(root, 'checkers/python/g17check.py'), 'first.g17m', '--environment', 'first.g17env'], {
    cwd: workspace, encoding: 'utf8', timeout: 120000,
  });
  if (independent.error) throw independent.error;
  assert.equal(independent.status, 0, independent.stderr || independent.stdout);
  const missing = run(['check', '--foundation', 'ZF', '--module-root', join(root, 'lib'), 'client/Main.g17'], false);
  assert.match(missing.stderr + missing.stdout, /Shared\.Sets/);
  console.log(JSON.stringify({ ok: true, checks: ['external two-project imports', 'goal-directed specialization', 'no admissions', 'complete ZF audit', 'byte-identical repeated exports', 'independent Python proof-tape replay', 'missing dependency rejected'], independent: independent.stdout.trim() }, null, 2));
} finally {
  rmSync(workspace, { recursive: true, force: true });
}
