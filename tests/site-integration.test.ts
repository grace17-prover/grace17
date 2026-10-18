// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import vm from 'node:vm';
import { resolveWorkbenchLink, workbenchLink } from '../workbench/deep-links.js';

const file = 'lib/Example.g17';
const source = 'module Example\nnamespace Example\ntheorem α\n  shows ∀ x, x = x\nproof\n  intro x\n  rfl\nend Example\n';
const library = new Map([[file, source]]);
test('proof links work at root and under arbitrary hosting prefixes', () => {
  for (const prefix of ['/', '/workbench/', '/preview/workbench/']) {
    const url = new URL(workbenchLink(file, 3, prefix), 'https://grace17.org');
    assert.deepEqual(resolveWorkbenchLink(url.href, library), { file, source, line: 3 });
    assert.equal(resolveWorkbenchLink(`https://grace17.org${prefix}#file=${encodeURIComponent(file)}&symbol=Example.α`, library)?.line, 3);
  }
  assert.equal(resolveWorkbenchLink('https://grace17.org/workbench/', library), null);
  for (const query of ['file=missing', `file=${file}&line=0`, `file=${file}&line=99`, `file=${file}&symbol=missing`]) {
    assert.throws(() => resolveWorkbenchLink(`https://grace17.org/#${query}`, library));
  }
});
test('service-worker install resolves shell and editor assets inside its hosting scope', async () => {
  const code = readFileSync(new URL('../workbench/service-worker.template.js', import.meta.url), 'utf8');
  for (const pathname of ['/workbench/', '/preview/workbench/']) {
    const listeners: any = {}, assets: string[] = [], deleted: string[] = [];
    const origin = 'https://grace17.org';
    let pending: Promise<void>;
    const cache = { addAll: async (urls: string[]) => assets.push(...urls), put: async () => {} };
    vm.runInNewContext(code, {
      URL, self: { location: new URL(`${origin}${pathname}service-worker.js`), addEventListener: (n: string, f: any) => listeners[n] = f, skipWaiting() {}, clients: { claim() {} } },
      caches: { open: async () => cache, keys: async () => [`grace17-workbench-${pathname}-old`, 'unrelated-site-cache'], delete: async (key: string) => deleted.push(key) },
      fetch: async (url: string) => {
        assert.equal(url, `${origin}${pathname}generated/monaco-assets.json`);
        return { clone() { return this; }, json: async () => ['/generated/monaco/vs/editor/editor.main.js'] };
      },
    });
    listeners.install({ waitUntil(p: Promise<void>) { pending = p; } }); await pending!;
    assert(assets.length > 20); assert(assets.every(url => url.startsWith(origin + pathname)));
    listeners.activate({ waitUntil(p: Promise<void>) { pending = p; } }); await pending!;
    assert.deepEqual(deleted, [`grace17-workbench-${pathname}-old`]);
    let intercepted = false;
    listeners.fetch({ request: { method: 'GET', url: origin + '/cumulus/' }, respondWith() { intercepted = true; } });
    assert.equal(intercepted, false);
  }
});
test('Workbench entry assets and PWA manifest are portable relative URLs', () => {
  const html = readFileSync(new URL('../workbench/index.html', import.meta.url), 'utf8');
  assert.doesNotMatch(html, /(?:src|href)="\//);
  const manifest = JSON.parse(readFileSync(new URL('../workbench/manifest.webmanifest', import.meta.url), 'utf8'));
  assert.equal(manifest.start_url, './');
  assert.equal(manifest.icons[0].src, './assets/grace-icon.svg');
});
test('inline source links round-trip Unicode proofs and reject malformed names', async () => {
  const { workbenchSourceLink, encodeSource } = await import('../workbench/deep-links.js');
  const href = workbenchSourceLink('Probe.g17', source, '/docs/../workbench/', 4);
  const resolved = resolveWorkbenchLink(new URL(href, 'https://grace17.org').href, library);
  assert.deepEqual(resolved, { file: 'Probe.g17', source, line: 4, inline: true });
  assert.throws(() => resolveWorkbenchLink(`https://grace17.org/workbench/#name=../x.g17&source=${encodeSource('a')}`, library));
  assert.throws(() => resolveWorkbenchLink('https://grace17.org/workbench/#source=%%%', library));
  assert.throws(() => resolveWorkbenchLink(`https://grace17.org/workbench/#line=99&source=${encodeSource('a')}`, library));
});
