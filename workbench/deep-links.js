// Stable links from static documentation into the bundled local proof assistant.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { scanSearchDeclarations } from './library-search.js';
export function workbenchLink(file, line = 1, base = "./workbench/", view) {
  return `${base}#${new URLSearchParams({ file, line: String(line), ...(view ? { view } : {}) })}`;
}

// Inline sources travel in the URL fragment as base64url UTF-8, so documentation
// can open any code block in the Workbench without a server or a bundled file.
export function encodeSource(text) {
  const bytes = new TextEncoder().encode(text);
  let binary = "";
  for (const byte of bytes) binary += String.fromCharCode(byte);
  return btoa(binary).replaceAll("+", "-").replaceAll("/", "_").replace(/=+$/, "");
}
export function decodeSource(value) {
  const base64 = value.replaceAll("-", "+").replaceAll("_", "/");
  const padded = base64 + "=".repeat((4 - base64.length % 4) % 4);
  const binary = atob(padded);
  return new TextDecoder().decode(Uint8Array.from(binary, c => c.charCodeAt(0)));
}
export function workbenchSourceLink(name, source, base = "./workbench/", line = 1) {
  return `${base}#${new URLSearchParams({ name, line: String(line), source: encodeSource(source) })}`;
}
export function resolveWorkbenchLink(href, library) {
  const url = new URL(href);
  const params = new URLSearchParams(url.hash.slice(1) || url.search.slice(1));
  const inline = params.get("source");
  if (inline !== null) {
    const name = params.get("name") || "Scratch.g17";
    if (!/^[A-Za-z0-9_.-]+\.g17$/.test(name)) throw new Error("Invalid inline file name.");
    let source;
    try { source = decodeSource(inline); } catch { throw new Error("Invalid inline source."); }
    const line = Number(params.get("line") || 1);
    if (!Number.isSafeInteger(line) || line < 1 || line > source.split("\n").length) throw new Error("Invalid source line.");
    const view = params.get("view");
    return { file: name, source, line, inline: true, ...(view ? { view } : {}) };
  }
  const file = params.get("file");
  if (!file) return null;
  if (!library.has(file)) throw new Error('This file is not in the bundled library.');
  const source = library.get(file);
  let line = Number(params.get('line') || 1);
  const symbol = params.get('symbol');
  if (symbol) {
    const matches = scanSearchDeclarations(file, source).filter(d => d.name === symbol || d.short === symbol);
    if (matches.length !== 1) throw new Error('The declaration is missing or ambiguous.');
    line = matches[0].line;
  }
  if (!Number.isSafeInteger(line) || line < 1 || line > source.split('\n').length) throw new Error('Invalid source line.');
  const view = params.get("view");
  return { file, source, line, ...(view ? { view } : {}) };
}
