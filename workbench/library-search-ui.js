// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Local discovery is independent of the proof-checking worker.
export function installLibrarySearch({ getFiles, navigate, focusEditor }) {
  const dialog = document.querySelector('#librarySearchDialog');
  const input = document.querySelector('#librarySearchInput');
  const status = document.querySelector('#librarySearchStatus');
  const results = document.querySelector('#librarySearchResults');
  let worker, generation = 0, timer;
  function search(sync = false) {
    const id = ++generation;
    status.textContent = 'Searching…';
    results.replaceChildren();
    if (!worker) {
      worker = new Worker(new URL('./library-search-worker.js', import.meta.url), { type: 'module' });
      worker.addEventListener('error', () => {
        status.textContent = 'Search could not start. Close and reopen search to retry.';
        worker.terminate(); worker = undefined;
      });
      worker.addEventListener('message', ({ data }) => {
        if (data.id !== generation || !dialog.open) return;
        if (data.error) { status.textContent = data.error; return; }
        const { total, indexed, milliseconds, results: hits } = data.result;
        status.textContent = `${total} results · ${indexed.toLocaleString()} declarations · ${milliseconds.toFixed(1)} ms${total > hits.length ? ' · showing first ' + hits.length : ''}`;
        for (const hit of hits) {
          const row = document.createElement('article'); row.className = 'library-search-result';
          const open = document.createElement('button'); open.className = 'search-declaration'; open.textContent = hit.name;
          open.addEventListener('click', () => { dialog.close(); navigate(hit); });
          const meta = document.createElement('small'); meta.textContent = `${hit.kind} · ${hit.module} · line ${hit.line}`;
          const signature = document.createElement('pre'); signature.textContent = hit.signature;
          const copy = document.createElement('button'); copy.className = 'quiet'; copy.textContent = 'Copy name';
          copy.setAttribute('aria-label', `Copy ${hit.name}`);
          copy.addEventListener('click', async () => {
            try { await navigator.clipboard.writeText(hit.name); copy.textContent = 'Copied'; }
            catch { status.textContent = 'Clipboard unavailable. Select and copy the declaration name.'; }
          });
          row.append(open, copy, meta, signature);
          if (hit.context) { const details = document.createElement('details'), summary = document.createElement('summary'), context = document.createElement('pre'); summary.textContent = 'Section context'; context.textContent = hit.context; details.append(summary, context); row.append(details); }
          if (hit.documentation) { const docs = document.createElement('p'); docs.textContent = hit.documentation; row.append(docs); }
          results.append(row);
        }
        if (!hits.length) results.textContent = 'No matching declarations. Try fewer terms or a shorter name.';
      });
      sync = true;
    }
    worker.postMessage({ id, query: input.value, ...(sync ? { files: getFiles() } : {}) });
  }
  function open() { clearTimeout(timer); if (!dialog.open) dialog.showModal(); input.focus(); input.select(); search(true); }
  document.querySelector('#librarySearch').addEventListener('click', open);
  document.querySelector('#closeLibrarySearch').addEventListener('click', () => dialog.close());
  dialog.addEventListener('close', () => { clearTimeout(timer); generation++; focusEditor(); });
  dialog.addEventListener('click', event => { if (event.target === dialog) dialog.close(); });
  input.addEventListener('input', () => { generation++; clearTimeout(timer); timer = setTimeout(() => search(), 120); });
  input.addEventListener('keydown', event => {
    if (event.key === 'ArrowDown') { event.preventDefault(); results.querySelector('button')?.focus(); }
    if (event.key === 'Enter') { event.preventDefault(); clearTimeout(timer); search(); }
  });
  document.addEventListener('keydown', event => {
    if ((event.ctrlKey || event.metaKey) && event.shiftKey && event.key.toLowerCase() === 'f') {
      if (document.querySelector('dialog[open]') && !dialog.open) return;
      event.preventDefault(); open();
    }
  });
}
