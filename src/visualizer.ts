// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { formatFormula, formatTerm } from "./pretty.ts";
import type { ExportedProof } from "./export.ts";
import { formulaEquals, type Term } from "./ast.ts";
import type { TacticStateSnapshot, TacticTrace } from "./tactic-trace.ts";

/** Render a self-contained, dependency-free proof explorer. */
export function renderProofHtml(exported: ExportedProof): string {
  const visited = new Set<number>();
  const renderNode = (id: number): string => {
    if (visited.has(id)) return `<a class="shared" href="#kernel-step-${id}">↩ shared judgment #${id}</a>`;
    visited.add(id);
    const judgment = exported.trace.nodes[id]!;
    const payload = exported.proof.nodes[judgment.proofNode]!.payload as Record<string, unknown>;
    const children = judgment.children.map(renderNode).join("");
    const context = judgment.assumptions.length === 0
      ? '<span class="empty-context">∅</span>'
      : judgment.assumptions.map((formula, index) => `<span class="assumption"><span>${index + 1}</span>${escapeHtml(formatFormula(formula))}</span>`).join("");
    return `<details class="proof-node" id="kernel-step-${id}" open>
      <summary><span class="node-id">#${id}</span><span class="rule">${escapeHtml(ruleLabel(payload))}</span><span class="summary-text">${escapeHtml(ruleDetail(payload))}</span></summary>
      <div class="node-body"><div class="judgment"><div class="context"><span class="judgment-label">Context Γ</span><div class="context-items">${context}</div></div><div class="turnstile">⊢</div><div class="goal"><span class="judgment-label">Goal / result</span><div class="formula">${escapeHtml(formatFormula(judgment.conclusion))}</div></div></div>${children ? `<div class="premise-label">Premise${judgment.children.length === 1 ? "" : "s"}</div>${children}` : '<span class="leaf">✓ no remaining premises</span>'}<details class="raw"><summary>kernel data</summary><pre>${escapeHtml(JSON.stringify({ judgment, proof: payload }, null, 2))}</pre></details></div>
    </details>`;
  };
  const dependencies = [
    ...exported.dependencies.axioms.map(name => `<span class="dependency axiom">axiom · ${escapeHtml(name)}</span>`),
    ...exported.dependencies.theorems.map(name => `<span class="dependency theorem">theorem · ${escapeHtml(name)}</span>`),
    ...exported.dependencies.definitions.map(name => `<span class="dependency definition">definition · ${escapeHtml(name)}</span>`),
  ].join("") || '<span class="dependency">no named dependencies</span>';
  const tactics = exported.tactics ? renderTacticTrace(exported.tactics) : "";
  const kernelOpen = exported.tactics ? "" : " open";

  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escapeHtml(exported.theorem)} · GRACE17 proof</title>
<style>
:root{color-scheme:light dark;--bg:#f3f7f9;--panel:#fff;--ink:#101820;--muted:#5d6b74;--line:#cbd7dd;--accent:#006f9e;--soft:#e3f4f7;--goal:#edf7fa;--success:#087f87;--axiom:#9b4f20;--theorem:#087f87;--definition:#286ca8} @media(prefers-color-scheme:dark){:root{--bg:#070b0e;--panel:#0c1217;--ink:#d8e2e7;--muted:#7d8d96;--line:#40515c;--accent:#57f4ff;--soft:#10283a;--goal:#0d1b24;--success:#57f4ff;--axiom:#ef9a73;--theorem:#57f4ff;--definition:#65aef2}}
*{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 ui-sans-serif,system-ui,-apple-system,"Segoe UI",sans-serif} main{max-width:1000px;margin:0 auto;padding:32px 20px 64px} header{border-bottom:1px solid var(--line);padding-bottom:24px;margin-bottom:24px}.brand{font-size:12px;letter-spacing:.14em;text-transform:uppercase;color:var(--muted)}h1{font-size:26px;font-weight:600;margin:6px 0 12px}.statement{font:18px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;background:var(--panel);border:1px solid var(--line);padding:16px;border-radius:10px;overflow-wrap:anywhere}.meta{display:flex;gap:14px;flex-wrap:wrap;margin-top:12px;color:var(--muted);font-size:12px}.meta code{color:var(--ink)}h2{font-size:15px;font-weight:600;margin:26px 0 10px}.dependencies{display:flex;gap:7px;flex-wrap:wrap}.dependency{border:1px solid var(--line);border-radius:999px;padding:4px 9px;font-size:12px;background:var(--panel)}.dependency.axiom{color:var(--axiom)}.dependency.theorem{color:var(--theorem)}.dependency.definition{color:var(--definition)}.tactic-trace{margin-top:12px}.initial-state{margin-bottom:10px}.state-caption,.goal-caption{color:var(--muted);font-size:11px;letter-spacing:.08em;text-transform:uppercase}.tactic-step{display:grid;grid-template-columns:minmax(210px,.8fr) minmax(300px,1.7fr);border-top:1px solid var(--line);padding:12px 0;gap:16px}.tactic-command{display:flex;align-items:baseline;gap:9px;min-width:0}.line-number{color:var(--muted);font:11px ui-monospace,monospace}.tactic-command code{color:var(--accent);font:14px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;overflow-wrap:anywhere}.surface-state{display:flex;flex-direction:column;gap:8px}.surface-goal{background:var(--goal);border-radius:8px;padding:10px 12px}.surface-goal.focused{box-shadow:inset 3px 0 0 var(--accent)}.goal-caption{display:flex;justify-content:space-between;margin-bottom:4px}.focused-label{color:var(--accent)}.surface-formula{font:15px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;overflow-wrap:anywhere}.surface-context{margin-top:7px;padding-top:7px;border-top:1px solid var(--line);display:flex;flex-direction:column;gap:3px;font:12px/1.45 ui-monospace,SFMono-Regular,Menlo,monospace}.local-name{color:var(--accent)}.proof-complete{color:var(--success);font-weight:600;padding:8px 0}.kernel-proof{margin-top:30px;border-top:1px solid var(--line);padding-top:14px}.kernel-proof>summary{cursor:pointer;font-weight:600;color:var(--accent)}.kernel-note{color:var(--muted);font-weight:400;margin-left:6px}.toolbar{display:flex;gap:8px;margin:20px 0 10px}button{font:inherit;color:var(--ink);background:var(--panel);border:1px solid var(--line);border-radius:7px;padding:6px 10px;cursor:pointer}button:hover{background:var(--soft)}.proof-node{margin:7px 0 7px 18px;border-left:2px solid var(--line)}.proof-node>summary{display:flex;align-items:baseline;gap:9px;cursor:pointer;padding:7px 10px;list-style:none}.proof-node>summary::-webkit-details-marker{display:none}.proof-node>summary:before{content:"▸";color:var(--muted);width:10px}.proof-node[open]>summary:before{content:"▾"}.proof-node:target>summary{background:var(--soft)}.node-id{font:12px ui-monospace,monospace;color:var(--muted)}.rule{font-weight:600;color:var(--accent)}.summary-text{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;color:var(--muted);overflow-wrap:anywhere}.node-body{padding:0 0 4px 12px}.judgment{display:grid;grid-template-columns:minmax(110px,.7fr) 24px minmax(220px,1.8fr);align-items:stretch;margin:2px 10px 10px 22px;border:1px solid var(--line);border-radius:8px;background:var(--panel);overflow:hidden}.context,.goal{padding:9px 11px}.goal{background:var(--goal)}.judgment-label,.premise-label{display:block;color:var(--muted);font-size:11px;letter-spacing:.08em;text-transform:uppercase;margin-bottom:3px}.turnstile{display:grid;place-items:center;color:var(--accent);font:20px ui-monospace,monospace;border-left:1px solid var(--line);border-right:1px solid var(--line)}.formula{font:15px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace;overflow-wrap:anywhere}.context-items{display:flex;flex-direction:column;gap:4px}.assumption{font:12px/1.4 ui-monospace,SFMono-Regular,Menlo,monospace;overflow-wrap:anywhere}.assumption>span{display:inline-block;color:var(--muted);min-width:18px}.empty-context{color:var(--muted);font:16px ui-monospace,monospace}.premise-label{margin:10px 0 0 28px}.leaf,.shared{display:block;margin:5px 0 8px 28px;color:var(--muted);font-size:12px}.shared{color:var(--accent);text-decoration:none}.raw{margin:5px 0 8px 22px;color:var(--muted);font-size:12px}.raw pre{background:var(--panel);border:1px solid var(--line);border-radius:7px;padding:10px;overflow:auto;color:var(--ink)}footer{margin-top:28px;color:var(--muted);font-size:12px}@media(max-width:680px){main{padding:20px 10px 40px}.tactic-step{grid-template-columns:1fr;gap:7px}.proof-node{margin-left:8px}.statement{font-size:15px}.summary-text{font-size:12px}.judgment{grid-template-columns:1fr;margin-left:12px}.turnstile{border:0;border-top:1px solid var(--line);border-bottom:1px solid var(--line);min-height:28px}}
</style></head><body><main>
<header><div class="brand">GRACE17 proof</div><h1>${escapeHtml(exported.theorem)}</h1><div class="statement">${escapeHtml(formatFormula(exported.statement))}</div><div class="meta">${exported.tactics ? `<span><code>${exported.tactics.steps.length}</code> tactic steps</span>` : ""}<span><code>${exported.proof.nodes.length}</code> primitive nodes</span><span>certificate <code>${escapeHtml(exported.proof.digest.slice(0,16))}…</code></span></div></header>
<section><h2>Trusted dependencies</h2><div class="dependencies">${dependencies}</div></section>
${tactics ? `<section><h2>Tactic proof</h2>${tactics}</section>` : ""}
<details class="kernel-proof"${kernelOpen}><summary>Drill into kernel proof <span class="kernel-note">${exported.proof.nodes.length} primitive nodes · ${exported.trace.nodes.length} judgments</span></summary><div class="toolbar"><button type="button" data-action="expand">Expand primitive proof</button><button type="button" data-action="collapse">Collapse primitive proof</button></div>${renderNode(exported.trace.root)}</details>
<footer>Environment <code>${escapeHtml(exported.environment)}</code><br>Envelope <code>${escapeHtml(exported.digest)}</code></footer>
</main><script>document.querySelector('[data-action="expand"]').onclick=()=>document.querySelectorAll('.proof-node').forEach(x=>x.open=true);document.querySelector('[data-action="collapse"]').onclick=()=>document.querySelectorAll('.proof-node,.raw').forEach(x=>x.open=false);</script></body></html>`;
}

function renderTacticTrace(trace: TacticTrace): string {
  const initial = `<div class="initial-state"><div class="state-caption">Initial goal</div>${renderTacticState(trace.initial)}</div>`;
  const steps = trace.steps.map((step, index) => `<div class="tactic-step"><div class="tactic-command"><span class="line-number">${step.line}</span><code>${escapeHtml(step.command)}</code></div>${renderTacticState(step.after, index + 1)}</div>`).join("");
  return `<div class="tactic-trace">${initial}${steps}</div>`;
}

function renderTacticState(state: TacticStateSnapshot, step?: number): string {
  if (state.goals.length === 0) return '<div class="surface-state"><div class="proof-complete">✓ No goals</div></div>';
  const goals = state.goals.map((item, index) => {
    const locals = item.locals.map(local => `<div><span class="local-name">${escapeHtml(local.name)}</span> : ${escapeHtml(formatFormula(local.formula))}</div>`);
    const unnamed = item.assumptions.filter(formula => !item.locals.some(local => formulaEquals(local.formula, formula)));
    const assumptions = unnamed.map((formula, assumption) => `<div><span class="local-name">h${assumption + 1}</span> : ${escapeHtml(formatFormula(formula))}</div>`);
    const context = [...assumptions, ...locals];
    return `<div class="surface-goal${index === 0 ? " focused" : ""}"><div class="goal-caption"><span>${state.goals.length === 1 ? (step ? `After step ${step}` : "Goal") : `Goal ${index + 1} of ${state.goals.length}`}</span>${index === 0 ? '<span class="focused-label">focused</span>' : ""}</div>${context.length ? `<div class="surface-context">${context.join("")}</div>` : ""}<div class="surface-formula">⊢ ${escapeHtml(formatFormula(item.goal))}</div></div>`;
  }).join("");
  return `<div class="surface-state">${goals}</div>`;
}

function ruleLabel(payload: Record<string, unknown>): string {
  const labels: Record<string, string> = {
    assumption: "assumption", axiom: "axiom", theorem: "theorem", definition: "definition", refl: "reflexivity",
    compute: "kernel computation", rationalClassCompute: "quotient rational computation",
    forallIntro: "∀ introduction", forallElim: "∀ elimination", impIntro: "→ introduction",
    impElim: "→ elimination", iffIntro: "↔ introduction", iffElimLeft: "↔ forward",
    iffElimRight: "↔ backward", andIntro: "∧ introduction", andElimLeft: "∧ left",
    andElimRight: "∧ right", orIntroLeft: "∨ left", orIntroRight: "∨ right",
    orElim: "∨ elimination", existsIntro: "∃ introduction", existsElim: "∃ elimination",
    falseElim: "⊥ elimination", dne: "double-negation elimination",
    symm: "symmetry", trans: "transitivity", congr: "congruence", eqElim: "equality elimination",
    induction: "structural induction", wellFoundedInduction: "well-founded induction",
  };
  return labels[String(payload.rule)] ?? String(payload.rule);
}

function ruleDetail(payload: Record<string, unknown>): string {
  if (typeof payload.name === "string") return payload.property ? `${payload.name}.${payload.property}` : payload.name;
  if (typeof payload.variable === "string") return payload.variable;
  if (payload.term && typeof payload.term === "object") return formatTerm(payload.term as Term);
  if (typeof payload.fn === "string") return payload.fn;
  if (typeof payload.constructor === "string") return payload.constructor;
  return "";
}

function escapeHtml(value: string): string {
  return value.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;");
}
