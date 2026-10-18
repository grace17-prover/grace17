// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Module navigation is independent of proof checking and its cached results.
// Reading a module's identity from its source is shared with the machine
// interface in src/library-search.ts.
import { indexModuleDocuments, moduleDocument } from "./generated/src/library-search.js";
export { indexModuleDocuments, moduleDocument };

const workspaceDocuments = new WeakMap();
function liveDocument(item) {
  const cached = workspaceDocuments.get(item);
  if (cached?.source === item.source && cached?.name === item.name) return cached.document;
  const document = moduleDocument(item.name, item.source);
  workspaceDocuments.set(item, { source: item.source, name: item.name, document });
  return document;
}

// An import is written relative to the importing module and read innermost
// first: inside Grace.Cumulus.Algebra.Group, `import Core` names
// Grace.Cumulus.Algebra.Group.Core, then Grace.Cumulus.Algebra.Core, and so
// on down to the bare name, exactly as the module loader resolves it.
export function importCandidates(current, raw) {
  const result = [];
  if (current) {
    const segments = current.split('.');
    for (let depth = segments.length; depth >= 1; depth--) result.push([...segments.slice(0, depth), raw].join('.'));
  }
  result.push(raw);
  return [...new Set(result)];
}

export function importSymbolAt(source, offset, workspace, bundled, documents = []) {
  const start = source.lastIndexOf('\n', offset - 1) + 1;
  const end = source.indexOf('\n', start);
  const line = source.slice(start, end < 0 ? source.length : end);
  const match = /^\s*import[ \t]+([^\s]+)[ \t]*(?:--.*)?\r?$/.exec(line);
  if (!match) return undefined;
  const tokenStart = start + line.indexOf(match[1]);
  if (offset < tokenStart || offset >= tokenStart + match[1].length) return undefined;
  const name = match[1];
  const current = moduleDocument('', source)?.module;
  const lookup = candidate => {
    const local = workspace.map(liveDocument).filter(item => item?.module === candidate);
    return local.length ? local : bundled.get(candidate) || documents.filter(item => item.module === candidate).map(item => moduleDocument(item.file, item.source)).filter(Boolean);
  };
  let resolved = name;
  let candidates = [];
  for (const candidate of importCandidates(current, name)) {
    candidates = lookup(candidate);
    if (candidates.length) { resolved = candidate; break; }
  }
  const doc = candidates.length === 1 ? candidates[0] : undefined;
  return {
    name: resolved, short: name, kind: 'module', token: { text: name, start: tokenStart, end: tokenStart + name.length },
    info: doc ? `module ${resolved}\n${doc.file}${doc.header ? `\n\n${doc.header}` : ''}`
      : candidates.length ? `Ambiguous module ${resolved}:\n${candidates.map(item => item.file).join('\n')}`
        : `Module ${name} is not available in the current workspace or loaded libraries.`,
    file: doc?.file, line: doc?.line, document: doc,
  };
}
