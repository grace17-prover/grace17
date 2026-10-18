// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Render docs/tactics.md from the Workbench Help source, so the tactic
// reference on the website and the Help panel can never disagree.
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { helpInferenceRule, tacticGuideSections } from "../workbench/tactics-guide.js";
import { tacticReferenceNotes } from "../workbench/tactics-reference.js";
import { slugify } from "./site-render.ts";

interface Rule { premises: string[]; conclusion: string; label: string; side?: string }
interface Entry { syntax: string; summary: string; detail: string; example?: string; forms?: string[]; illustrative?: boolean }
interface Section { id: string; kind?: string; title: string; intro: string; entries: Entry[] }

const sections = (tacticGuideSections as Section[]).filter(section => section.id !== "language" && section.kind !== "language");

function schema(rule: Rule): string {
  const premises = rule.premises.length ? rule.premises.join("    ") : "(no premises)";
  const width = Math.max([...premises].length, [...rule.conclusion].length);
  const line = "─".repeat(width);
  const side = rule.side ? `\n${rule.side}` : "";
  return `${premises}\n${line}  ${rule.label}\n${rule.conclusion}${side}`;
}

function entry(item: Entry): string {
  const notes = tacticReferenceNotes(item.syntax) as string[];
  const inference = helpInferenceRule(item.syntax) as (Rule & { variants?: Rule[] }) | undefined;
  const variants = inference?.variants ?? (inference ? [inference] : []);
  let out = `### \`${item.syntax}\`\n\n**${item.summary}** ${item.detail}\n`;
  for (const note of notes) out += `\n${note}\n`;
  // An illustrative example names facts that exist only in its story; it is
  // rendered without a Workbench button.
  if (item.example) out += `\n\`\`\`g17${item.illustrative ? " fragment" : ""}\n${item.example}\n\`\`\`\n`;
  if (variants.length) out += `\nRule schema:\n\n\`\`\`text\n${variants.map(schema).join("\n\n")}\n\`\`\`\n`;
  return out;
}

export function renderTacticsDoc(): string {
  let out = `# Tactic reference

Every tactic in Grace17, organized as the Workbench **Help** panel presents
them: the first moves, logic and witnesses, changing the view, search and
automation, arithmetic, shaping a development, and induction. This page is
rendered from the Help source by \`npm run docs:tactics\`, so the two never
disagree. For a guided tour of writing proofs, read
[Proving theorems in Grace17](proving.md); for declarations, see
[definitions](definitions.md); for types and instances, see
[types](types.md).

Tactics are not part of the trusted kernel. They transform goals and build a
proof term, and the kernel checks that term from scratch before admitting the
theorem. A broken or hostile tactic can fail, exhaust its budget, or produce a
rejected proof; it cannot prove a false statement. Every entry below therefore
ends with the natural-deduction rule schema its proof term reduces to, with
\`Γ\` standing for the current local context.

## Conventions

- Almost always, we prefer proofs with one tactic per line. You can of
  course change this as you wish, for example by using semicolons to put
  several tactics on the same line. A leading \`.\` marks the next focused
  subgoal.
- Transformation tactics accept an \`at h\` suffix to act on a named local fact
  instead of the goal: \`unfold Subset at hAB\`, \`rw hxy at h\`,
  \`simp [add] at h\`, \`ring_nf at h\`, \`symm at h\`.
- A proof expression is a fact optionally applied to arguments: mathematical
  terms after \`at\`, checked premises after \`with\`, \`.forward\` and
  \`.backward\` for the directions of an equivalence, and \`.left\` and
  \`.right\` for the sides of a conjunction. The same expression grammar is
  used by \`exact\`, \`show\`, \`apply\`, \`have\`, \`specialize\`, \`refine\`,
  and \`calc\` justifications.
- \`with *\` fills omitted premises from checked local evidence and stops at a
  source theorem's \`shows\`; \`with *{n}\` fills exactly \`n\` premises.

## Command index

| Section | Commands |
|---|---|
`;
  for (const section of sections) {
    // Each command links to its own section, whose anchor is the slug of its syntax.
    out += `| [${section.title}](#${section.title.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "")}) | ${section.entries.map(item => `[\`${item.syntax.replace(/\|/g, "\\|")}\`](#${slugify(item.syntax)})`).join(", ")} |\n`;
  }
  for (const section of sections) {
    out += `\n## ${section.title}\n\n${section.intro}\n\n`;
    out += section.entries.map(entry).join("\n");
  }
  return out;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const rendered = renderTacticsDoc();
  if (process.argv.includes("--check")) {
    if (readFileSync("docs/tactics.md", "utf8") !== rendered) throw new Error("docs/tactics.md is stale; run npm run docs:tactics");
    console.log("docs/tactics.md matches the Workbench Help");
  } else { writeFileSync("docs/tactics.md", rendered); console.log("Updated docs/tactics.md"); }
}
