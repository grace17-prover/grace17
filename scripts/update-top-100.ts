// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Keep the public catalogue's formal statements synchronized with checked sources.
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";

export function renderTop100(): string {
  const entries = JSON.parse(readFileSync("docs/top-100.json", "utf8")) as Array<{
    number: number; title: string; status: "verified" | "scoped" | "planned";
    informal: string; scope: string;
    proofs: Array<{ file: string; theorem: string }>;
  }>;
  const seen = new Set<number>();
  const counts = { verified: 0, scoped: 0, planned: 0 };
  for (const entry of entries) {
    if (!Number.isInteger(entry.number) || entry.number < 1 || entry.number > 100 || seen.has(entry.number))
      throw new Error(`Invalid or duplicate Top 100 number: ${entry.number}`);
    if (!(entry.status in counts)) throw new Error(`Unknown status: ${entry.status}`);
    if (entry.status !== "planned" && !entry.proofs.length) throw new Error(`Missing proof: ${entry.number}`);
    seen.add(entry.number); counts[entry.status]++;
  }
  const labels = { verified: "✅ Verified", scoped: "◐ Scoped result", planned: "○ Planned" };
  const statement = (file: string, name: string) => {
    const lines = readFileSync(file, "utf8").split("\n");
    // An instance is a checked theorem too, registered for search.
    const start = lines.findIndex(line => ["theorem", "instance"].some(keyword => line.startsWith(`${keyword} ${name} `) || line === `${keyword} ${name}`));
    if (start < 0) throw new Error(`Missing theorem ${name} in ${file}`);
    const end = lines.findIndex((line, i) => i > start && line === "proof");
    if (end < 0) throw new Error(`Missing proof for ${name}`);
    return { text: lines.slice(start, end).join("\n"), line: start + 1 };
  };
  let out = `# Cumulus · The Top 100 Theorems

Foundational mathematics in **Grace17**, from sets to working proofs.

**${counts.verified}/100 verified entries**

Numbering follows [Freek Wiedijk's Formalizing 100 Theorems](https://www.cs.ru.nl/~freek/100/).

## At a glance

| No. | Theorem |
| ---: | --- |
`;
  for (const e of entries) out += `| ${e.number} | [${e.title}](#thm-${e.number}) |\n`;
  out += `
## Statements and proofs
`;
  for (const e of entries) {
    out += `\n<a id="thm-${e.number}"></a>\n\n### ${e.number}. ${e.title}\n\n**Informal.** ${e.informal}\n\n**Scope.** ${e.scope}\n`;
    for (const proof of e.proofs) {
      const value = statement(proof.file, proof.theorem);
      out += `\n[Proof: ${proof.theorem}](../${proof.file}#L${value.line})\n\n<details open>\n<summary>Formal Grace17 statement</summary>\n\n<!-- cumulus-source: ${proof.file} -->\n\`\`\`g17\n${value.text}\n\`\`\`\n\n</details>\n`;
    }
    out += "\n[Back to overview](#at-a-glance)\n";
  }
  out += `
## Beyond the numbered list

The library also grows in ways the scoreboard does not count.
The **two-modulus Chinese remainder theorem** is one example:
for coprime integers m,n and arbitrary residues a,b, a simultaneous solution exists and is unique modulo m*n.
Its explicit construction uses Bézout coefficients.
`;
  for (const name of ["ChineseRemainder.exists", "ChineseRemainder.unique"]) {
    const file = "lib/Grace/Cumulus/NumberTheory/ChineseRemainder.g17";
    const value = statement(file, name);
    out += `\n[Proof: ${name}](../${file}#L${value.line})\n\n<!-- cumulus-source: ${file} -->\n\`\`\`g17\n${value.text}\n\`\`\`\n`;
  }
  out += `
**Orthogonal projection onto a line** is constructed for arbitrary finite
real vectors with a nonzero direction. Its residual is orthogonal, and the
projection uniquely minimizes squared distance along that line. Its residual
also gives a Pythagorean decomposition, and projection is idempotent.
`;
  for (const name of ["lineProjection.orthogonal", "lineProjection.minimum", "lineProjection.unique_minimizer", "orthogonalResidual.pythagorean", "lineProjection.idempotent"]) {
    const file = "lib/Grace/Cumulus/LinearAlgebra/Projection.g17";
    const value = statement(file, name);
    out += `\n[Proof: ${name}](../${file}#L${value.line})\n\n<!-- cumulus-source: ${file} -->\n\`\`\`g17\n${value.text}\n\`\`\`\n`;
  }
  out += `
Try [ProjectionStarter.g17](../examples/ProjectionStarter.g17).

Successive removals along perpendicular directions preserve earlier
orthogonality and commute coordinatewise.
The two-direction Bessel bound also proves that the captured squared lengths
cannot exceed the original squared length. See
[OrthogonalizationStarter.g17](../examples/OrthogonalizationStarter.g17). 
`;
  out += `
Try [ChineseRemainderStarter.g17](../examples/ChineseRemainderStarter.g17).
Other developments include verified Dijkstra, executable Gaussian elimination, Euclidean centers,
compactness, uniform continuity, and modular inverses. See [cumulus.md](cumulus.md).

## Maintaining this page

1. Add or update the scope audit in [top-100.json](top-100.json).
2. Give every completed or scoped entry an existing theorem and source path.
3. Run \`npm run docs:top100\`; the formal statements and line links regenerate together.
4. Run \`npm run docs:top100:check\` and the relevant proof and replay checks.
`;
  return out;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const rendered = renderTop100();
  if (process.argv.includes("--check")) {
    if (readFileSync("docs/top-100.md", "utf8") !== rendered) throw new Error("docs/top-100.md is stale; run npm run docs:top100");
    console.log("Top 100 statements, proof links, and counts are current");
  } else { writeFileSync("docs/top-100.md", rendered); console.log("Updated docs/top-100.md"); }
}
