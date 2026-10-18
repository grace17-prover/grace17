// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { highlightGrace17 } from "../workbench/tactics-guide.js";
const input = document.querySelector('#search');
const status = document.querySelector('#search-status');
const results = document.querySelector('#results');
const normalize = value => value.normalize('NFKC').toLocaleLowerCase('en');
try {
  const response = await fetch('./declarations.json');
  if (!response.ok) throw new Error('Index unavailable');
  const records = (await response.json()).map(item => ({ ...item, text: normalize(`${item.name} ${item.signature} ${item.context}`) }));
  function render() {
    const terms = normalize(input.value.trim()).split(/\s+/).filter(Boolean);
    results.replaceChildren();
    if (!terms.length) { status.textContent = `${records.length.toLocaleString()} declarations. Enter a name or words from a statement, or browse modules below.`; return; }
    const matches = records.filter(r => terms.every(t => r.text.includes(t)));
    status.textContent = `${matches.length} matches${matches.length > 60 ? ' · showing the first 60; add words to narrow the search' : ''}`;
    for (const item of matches.slice(0, 60)) {
      const article = document.createElement('article'); article.className = 'result';
      const link = document.createElement('a'); link.href = item.href; link.textContent = item.name;
      const run = document.createElement('a'); run.href = item.run; run.textContent = 'Open in Workbench';
      const head = document.createElement("div"); head.className = "result-head"; run.className = "action run";
      const pre = document.createElement("pre"); const code = document.createElement("code");
      code.innerHTML = highlightGrace17([item.context, item.signature].filter(Boolean).join("\n")); pre.append(code);
      head.append(link, run); article.append(head, pre); results.append(article);
    }
  }
  const initial = new URLSearchParams(location.search).get("q");
  if (initial) input.value = initial;
  input.addEventListener("input", () => { render(); history.replaceState(null, "", input.value.trim() ? `?q=${encodeURIComponent(input.value.trim())}` : location.pathname); });
  render();
} catch (error) { status.textContent = 'Search could not load. You can still browse all source modules below.'; }
