#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bring documentation code to the library's current proof style. Verbatim
// library excerpts (marked `cumulus-source`) are replaced by the current text
// of the same declaration; other `g17` blocks and example files get the same
// rewrites as scripts/shorten-proofs.ts. Run `npm run check:site` afterwards
// to verify the rewritten blocks, since this script does not elaborate them.
//
//   node scripts/shorten-docs.ts [--write] docs/*.md examples/*.g17

import { readFileSync, writeFileSync } from "node:fs";
import { proofRewrites } from "./shorten-proofs.ts";

const args = process.argv.slice(2);
const write = args.includes("--write");
const files = args.filter(item => item !== "--write");

function applyAll(lines: readonly string[]): string[] {
  const output: string[] = [];
  let cursor = 0;
  for (const rewrite of proofRewrites(lines)) {
    while (cursor < rewrite.start) output.push(lines[cursor++]!);
    output.push(...rewrite.replacement);
    cursor = rewrite.end;
  }
  while (cursor < lines.length) output.push(lines[cursor++]!);
  return output;
}

/** The current text of the declaration an excerpt starts with, or undefined. */
function currentExcerpt(source: string, excerpt: string): string | undefined {
  const lines = source.split("\n");
  const wanted = excerpt.split("\n");
  const start = lines.indexOf(wanted[0]!);
  if (start < 0) return undefined;
  // Statement-only excerpts are untouched by proof rewrites.
  if (!wanted.includes("proof")) return source.includes(excerpt) ? excerpt : undefined;
  let end = start + 1;
  while (end < lines.length && lines[end] !== "" && !/^(theorem|lemma|def|instance|predicate|class|end|section)\b/.test(lines[end]!)) end += 1;
  return lines.slice(start, end).join("\n");
}

let changedFiles = 0;
for (const file of files) {
  const original = readFileSync(file, "utf8");
  let text = original;
  if (file.endsWith(".g17")) {
    text = applyAll(original.split("\n")).join("\n");
  } else {
    text = text.replace(/<!-- cumulus-source: ([^\n]+) -->\n```g17\n([\s\S]*?)\n```/g, (whole, source: string, excerpt: string) => {
      const current = currentExcerpt(readFileSync(source, "utf8"), excerpt);
      if (current === undefined) { console.log(`${file}: excerpt from ${source} not found: ${excerpt.split("\n")[0]}`); return whole; }
      return `<!-- cumulus-source: ${source} -->\n\`\`\`g17\n${current}\n\`\`\``;
    });
    text = text.replace(/(^|\n)(```g17\n)([\s\S]*?)(\n```)/g, (whole, lead: string, open: string, body: string, close: string, offset: number) => {
      const before = text.slice(Math.max(0, offset - 60), offset);
      if (/cumulus-source: [^\n]+ -->\n?$/.test(before)) return whole;
      return `${lead}${open}${applyAll(body.split("\n")).join("\n")}${close}`;
    });
  }
  if (text !== original) {
    changedFiles += 1;
    const saved = original.split("\n").length - text.split("\n").length;
    console.log(`${file}: changed (${saved} lines saved)`);
    if (write) writeFileSync(file, text);
  }
}
console.log(`${changedFiles} files changed${write ? "" : "; rerun with --write to save"}`);
