// Validate generated local links and every documentation-to-Workbench target.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import assert from 'node:assert/strict';
import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';
import { resolveWorkbenchLink } from '../workbench/deep-links.js';
import { standardLibrary } from '../workbench/generated/shims/standard-library.js';
import { checkWorkbenchFiles, workbenchFailure } from '../src/workbench.ts';
const root = fileURLToPath(new URL('../build/site/', import.meta.url));
const walk = (dir: string): string[] => readdirSync(dir, { withFileTypes: true }).flatMap(e => e.isDirectory() ? walk(join(dir, e.name)) : [join(dir, e.name)]);
let links = 0, proofLinks = 0;
const cache = new Map<string, string>();
// Every inline Workbench link carries the exact text the button opens; check
// that text so a documentation fragment can never open as a failing proof.
const fragments = new Map<string, { readonly file: string; readonly source: string; readonly pages: Set<string> }>();
for (const file of walk(root).filter(p => p.endsWith('.html') && !p.includes('/workbench/generated/'))) {
  const html = readFileSync(file, 'utf8');
  const base = new URL(relative(root, file), 'https://preview.invalid/nested/site/');
  for (const match of html.matchAll(/(?:href|src)="([^"]+)"/g)) {
    const value = match[1].replaceAll('&amp;', '&');
    const target = new URL(value, base);
    if (target.origin !== base.origin) continue;
    assert(target.pathname.startsWith('/nested/site/'), `Escapes hosting prefix: ${file}: ${value}`);
    let path = join(root, decodeURIComponent(target.pathname.slice('/nested/site/'.length)));
    if (existsSync(path) && statSync(path).isDirectory()) path = join(path, 'index.html');
    assert(existsSync(path), `Missing target: ${file}: ${value}`); links++;
    if (target.pathname.includes("/workbench/") && (target.hash.includes("file=") || target.hash.includes("source="))) {
      const resolved = resolveWorkbenchLink(target.href, standardLibrary);
      assert(resolved); proofLinks++;
      // Example pages open complete example files, which the test suite checks
      // directly; documentation fragments are the links that need this check.
      if (resolved.inline && relative(root, file).startsWith('docs/')) {
        const key = `${resolved.file}\n${resolved.source}`;
        if (!fragments.has(key)) fragments.set(key, { file: resolved.file, source: resolved.source, pages: new Set() });
        fragments.get(key)!.pages.add(relative(root, file));
      }
    } else if (target.hash && path.endsWith('.html')) {
      if (!cache.has(path)) cache.set(path, readFileSync(path, 'utf8'));
      assert(cache.get(path)!.includes(`id="${decodeURIComponent(target.hash.slice(1))}"`), `Missing anchor: ${value}`);
    }
  }
}
const records = JSON.parse(readFileSync(join(root, 'cumulus/declarations.json'), 'utf8'));
for (const record of records) {
  assert.equal(resolveWorkbenchLink(new URL(record.run, 'https://preview.invalid/nested/site/cumulus/').href, standardLibrary)?.line, record.line);
}
const broken: string[] = [];
for (const fragment of fragments.values()) {
  let result: { ok: boolean; message?: string; line?: number };
  const started = performance.now();
  try { result = checkWorkbenchFiles([{ name: fragment.file, source: fragment.source }], 'ZFG', [fragment.file], { includeKernelDetails: false }); }
  catch (error) { result = workbenchFailure(error); }
  if (process.env.G17_CHECK_SITE_VERBOSE) console.error(`${result.ok ? 'ok  ' : 'FAIL'} ${(performance.now() - started).toFixed(0)} ms  ${[...fragment.pages][0]}: ${fragment.source.split('\n')[1]} | ${fragment.source.split('\n').find(line => /^(theorem|lemma|def|predicate|class|datatype|eval|notation|instance|noncomputable)\b/.test(line))}`);
  if (!result.ok) {
    const head = fragment.source.split('\n').find(line => /^(theorem|lemma|def|predicate|class|datatype|eval|notation|instance|noncomputable)\b/.test(line)) ?? fragment.source.split('\n')[0];
    broken.push(`${[...fragment.pages].join(', ')}: ${head}\n    line ${result.line}: ${result.message}`);
  }
}
if (broken.length) {
  console.error(`${broken.length} documentation fragment(s) fail to check:\n${broken.map(item => `  ${item}`).join('\n')}`);
  process.exit(1);
}
console.log(JSON.stringify({ ok: true, links, proofLinks, fragments: fragments.size, declarationTargets: records.length, hostingPrefix: '/nested/site/' }, null, 2));
