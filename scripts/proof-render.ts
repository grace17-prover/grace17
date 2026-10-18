// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Static renderings of checked kernel proofs for the website: the same
// natural-deduction derivation as a Fitch-style list of numbered lines with
// assumption rails, and as a Gentzen-style tree. Both are produced from the
// kernel proof DAG that the Workbench shows, so a page can carry the actual
// certificate of a theorem rather than a picture of one.
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { kernelFitchOrder } from "../workbench/editor-utils.js";
import { escape } from "./site-render.ts";

export interface KernelNode {
  readonly id: number;
  readonly rule: string;
  readonly ruleCode?: string;
  readonly ruleName?: string;
  readonly premiseLabels?: readonly string[];
  readonly sideConditions?: readonly string[];
  readonly arguments?: readonly { readonly name: string; readonly value: string }[];
  readonly assumptions: readonly string[];
  readonly conclusion: string;
  readonly children: readonly number[];
}

const root = resolve(fileURLToPath(import.meta.url), "../..");
const checked = new Map<string, Map<string, readonly KernelNode[]>>();

/** The kernel proof of one theorem of a checked file, by qualified or short name. */
export function kernelProof(file: string, theorem: string): readonly KernelNode[] | undefined {
  let proofs = checked.get(file);
  if (!proofs) {
    const source = readFileSync(resolve(root, file), "utf8");
    const result = checkWorkbenchFiles([{ name: file, source }], "ZFG", [file], { includeKernelDetails: true }) as { ok: boolean; theorems?: readonly { name: string; kernel?: readonly KernelNode[] }[] };
    if (!result.ok) throw new Error(`cannot check ${file} for proof rendering`);
    proofs = new Map((result.theorems ?? []).map(item => [item.name, item.kernel ?? []]));
    checked.set(file, proofs);
  }
  return proofs.get(theorem) ?? [...proofs.entries()].find(([name]) => name.endsWith(`.${theorem}`))?.[1];
}

/** Fitch style: numbered lines, premises before conclusions, assumption rails. */
export function renderFitch(nodes: readonly KernelNode[]): string {
  const ordered = kernelFitchOrder(nodes as never[]) as (KernelNode & { fitchLine: number })[];
  const byId = new Map(nodes.map(node => [node.id, node]));
  const contextKey = (node: KernelNode) => JSON.stringify(node.assumptions);
  const referenceById = new Map(ordered.map((node, index) => {
    let start = index;
    while (start > 0 && contextKey(ordered[start - 1]!) === contextKey(node)) start -= 1;
    const reference = start < index && node.assumptions.length > 0 ? `${ordered[start]!.fitchLine}–${node.fitchLine}` : String(node.fitchLine);
    return [node.id, reference];
  }));
  const cited = new Set(nodes.flatMap(node => node.children));
  const rootNode = nodes.find(node => !cited.has(node.id));
  const baseDepth = rootNode?.assumptions.length ?? 0;
  const lines = ordered.map((node, index) => {
    const depth = Math.max(0, node.assumptions.length - baseDepth);
    const scopeStart = depth > 0 && (index === 0 || contextKey(ordered[index - 1]!) !== contextKey(node));
    const rails = Array.from({ length: depth }, () => '<i class="fitch-rail"></i>').join("");
    const citations = node.children.map((id, premise) => `<a href="#nd-${id}" title="${escape(node.premiseLabels?.[premise] || `premise ${premise + 1}`)}">${referenceById.get(id) ?? "?"}</a>`).join(", ");
    const rule = escape(node.ruleCode || node.rule);
    const justification = citations ? `${rule} ${citations}` : rule;
    const args = node.arguments?.length ? `<dl class="fitch-arguments">${node.arguments.map(argument => `<div><dt>${escape(argument.name)}</dt><dd>${escape(argument.value)}</dd></div>`).join("")}</dl>` : "";
    const premises = node.children.map((id, premise) => {
      const child = byId.get(id);
      const inherited = node.assumptions.every((assumption, at) => child?.assumptions[at] === assumption);
      const discharged = inherited && child ? child.assumptions.slice(node.assumptions.length) : [];
      const brackets = discharged.length ? `<div class="nd-discharged">${discharged.map(assumption => `<code>[${escape(assumption)}]</code>`).join("")}</div>` : "";
      return `<div class="nd-premise">${brackets}<code>${escape(child?.conclusion ?? "premise")}</code><span>${escape(node.premiseLabels?.[premise] || `premise ${premise + 1}`)} · line ${referenceById.get(id) ?? "?"}</span></div>`;
    }).join("");
    const sideConditions = node.sideConditions?.length ? `<div class="nd-side-conditions"><span>${node.sideConditions.length === 1 ? "Side condition" : "Side conditions"}</span>${node.sideConditions.map(condition => `<code>${escape(condition)}</code>`).join("")}</div>` : "";
    const inference = `<div class="nd-inference"><div class="nd-rule"><div class="nd-premises">${premises}</div><div class="nd-rule-bar"><span></span><strong>${rule}</strong></div><code class="nd-conclusion">${escape(node.conclusion)}</code></div><aside class="nd-rule-aside"><strong>${escape(node.ruleName || node.rule)}</strong>${sideConditions}</aside></div>`;
    return `<details class="fitch-line${scopeStart ? " scope-start" : ""}${node.rule === "assumption" ? " assumption" : ""}" id="nd-${node.id}"><summary><span class="fitch-number">${node.fitchLine}</span><span class="fitch-formula"><span class="fitch-rails" aria-hidden="true">${rails}</span><code>${escape(node.conclusion)}</code></span><span class="fitch-justification"><strong>${justification}</strong><small>${escape(node.ruleName || node.rule)}</small></span></summary><div class="fitch-detail" style="--fitch-depth:${depth}">${inference}${args}</div></details>`;
  });
  return `<div class="fitch-proof">${lines.join("")}</div>`;
}

/** Gentzen style: the derivation unfolded as a tree, discharged assumptions in brackets. */
export function renderGentzen(nodes: readonly KernelNode[], limit = 400): string {
  const byId = new Map(nodes.map(node => [node.id, node]));
  const cited = new Set(nodes.flatMap(node => node.children));
  const rootNode = nodes.find(node => !cited.has(node.id)) ?? nodes[nodes.length - 1];
  if (!rootNode) return "";
  let budget = limit;
  const tree = (node: KernelNode, parent?: KernelNode): string => {
    budget -= 1;
    if (budget < 0) return `<span class="gz-elided" title="subproof elided">⋯</span>`;
    const discharged = parent && node.assumptions.every((assumption, at) => assumption === (parent.assumptions[at] ?? assumption))
      ? node.assumptions.slice(parent.assumptions.length) : [];
    const brackets = discharged.map(assumption => `<span class="gz-discharged">[${escape(assumption)}]</span>`).join("");
    if (node.rule === "assumption" || node.children.length === 0) {
      return `<div class="gz-node gz-leaf">${brackets}<span class="gz-formula">${node.rule === "assumption" ? `[${escape(node.conclusion)}]` : escape(node.conclusion)}</span>${node.rule !== "assumption" ? `<span class="gz-label">${escape(node.ruleCode || node.rule)}</span>` : ""}</div>`;
    }
    const premises = node.children.map(id => byId.get(id)).filter((child): child is KernelNode => Boolean(child)).map(child => tree(child, node)).join("");
    return `<div class="gz-node">${brackets}<div class="gz-premises">${premises}</div><div class="gz-rule"><span class="gz-concl">${escape(node.conclusion)}</span><span class="gz-label" title="${escape(node.ruleName || node.rule)}">${escape(node.ruleCode || node.rule)}</span></div></div>`;
  };
  const html = tree(rootNode);
  return `<div class="gentzen-proof${budget < 0 ? " elided" : ""}">${html}</div>`;
}

export function renderProof(file: string, theorem: string, style: string, caption?: string): string {
  const nodes = kernelProof(file, theorem);
  if (!nodes) throw new Error(`no kernel proof for ${theorem} in ${file}`);
  const parts: string[] = [];
  if (style === "gentzen" || style === "both") parts.push(`<div class="nd-view"><div class="nd-view-title">Gentzen style</div>${renderGentzen(nodes)}</div>`);
  if (style !== "gentzen") parts.push(`<div class="nd-view"><div class="nd-view-title">Fitch style</div>${renderFitch(nodes)}</div>`);
  const head = `<div class="nd-caption"><strong>${escape(theorem)}</strong> · ${nodes.length} kernel line${nodes.length === 1 ? "" : "s"}${caption ? ` · ${escape(caption)}` : ""}</div>`;
  return `<figure class="nd-figure">${head}${parts.join("")}</figure>`;
}
