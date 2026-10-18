// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { LibrarySearchWorkspace } from '../workbench/library-search.js';
import { standardLibrary } from '../workbench/generated/shims/standard-library.js';
const start = performance.now();
const workspace = new LibrarySearchWorkspace(standardLibrary);
const buildMs = performance.now() - start;
const queries = ['Nullstellensatz', 'name:mul module:Complex', 'kind:theorem symbol:IntegerDivides', 'module:Geometry pattern:"?x = ?x"', 'module:Polynomial name:translate', 'conclusion:"∃" -module:Core'];
const samples = [];
for (const query of queries) {
  const times = []; let result;
  for (let i = 0; i < 20; i++) { workspace.index.cache.clear(); result = workspace.index.search(query); times.push(result.milliseconds); }
  times.sort((a,b)=>a-b);
  const warm = workspace.index.search(query);
  samples.push({query, total: result.total, candidates: result.candidates, medianMs: times[10], p95Ms: times[19], cachedMs: warm.milliseconds});
}
console.log(JSON.stringify({modules:standardLibrary.size, declarations:workspace.index.records.size, buildMs, samples}, null, 2));
