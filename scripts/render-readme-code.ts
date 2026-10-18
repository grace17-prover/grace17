#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Render the README's Grace17 code blocks to SVG with the site's syntax
// colours, since the README's host highlights only the languages it knows.
// Each ```g17 fence that is followed by a `<!-- svg: name -->` marker is
// rendered to docs/images/readme-<name>.svg.
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { highlightGrace17 } from "../workbench/tactics-guide.js";

const root = fileURLToPath(new URL("..", import.meta.url));
const readme = readFileSync(`${root}README.md`, "utf8");
const colours: Record<string, string> = {
  keyword: "#57f4ff", tactic: "#65aef2", type: "#00c8d7", number: "#8bbef0", operator: "#aab8c0",
  comment: "#7f93a8", string: "#d9a441", connective: "#65aef2",
};
const ident = "#d8e2e7", ink = "#0c1b30", line = "#27405f";
const escapeXml = (text: string) => text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
const unescapeHtml = (text: string) => text.replace(/&quot;/g, "\"").replace(/&#39;/g, "'").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");

function render(code: string): string {
  const lines = code.replace(/\n$/, "").split("\n");
  const characterWidth = 8.43, lineHeight = 24, fontSize = 14, paddingX = 24, paddingY = 20;
  const width = Math.max(...lines.map(item => [...item].length)) * characterWidth + 2 * paddingX;
  const height = lines.length * lineHeight + 2 * paddingY;
  const highlighted = highlightGrace17(lines.join("\n")).split("\n");
  const spans = highlighted.map((item, index) => {
    const y = paddingY + (index + 1) * lineHeight - 7;
    const parts = item.split(/(<span class="g17-[a-z]+">.*?<\/span>)/g).map(part => {
      const match = /^<span class="g17-([a-z]+)">(.*)<\/span>$/.exec(part);
      if (match) return `<tspan fill="${colours[match[1]!] ?? ident}">${escapeXml(unescapeHtml(match[2]!))}</tspan>`;
      return escapeXml(unescapeHtml(part));
    }).join("");
    return `<text x="${paddingX}" y="${y}" xml:space="preserve">${parts}</text>`;
  }).join("\n");
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}" font-family="JetBrains Mono, Menlo, Consolas, monospace" font-size="${fontSize}" fill="${ident}">
<rect width="${width}" height="${height}" rx="10" fill="${ink}" stroke="${line}"/>
${spans}
</svg>
`;
}

const fence = /```g17\n([\s\S]*?)```\n<!-- svg: ([a-z0-9-]+) -->/g;
let count = 0;
for (const match of readme.matchAll(fence)) {
  writeFileSync(`${root}docs/images/readme-${match[2]}.svg`, render(match[1]!));
  count += 1;
}
console.log(`rendered ${count} README code blocks`);
