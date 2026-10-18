// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

const html = value => String(value).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));

export function axiomAuditSummary(audit) {
  const inherited = audit.hereditary.filter(name => !audit.direct.includes(name)).length;
  const choice = audit.hereditary.some(name => name === "set.choice" || name === "set.globalChoice");
  const choiceStatus = choice ? "Choice used" : audit.complete ? "no Choice" : "Choice undetermined";
  return `${audit.complete ? "Complete" : "Incomplete"} axiom audit · ${audit.direct.length} direct · ${inherited} inherited · ${choiceStatus}`;
}

export function renderAxiomAudit(audit) {
  const choice = audit.hereditary.some(name => name === "set.choice" || name === "set.globalChoice");
  const status = choice ? "Choice is used" : audit.complete ? "No Choice axiom used" : "Choice usage is undetermined";
  return `<p class="audit-status ${choice || !audit.complete ? "audit-attention" : ""}">${html(status)}</p>
    <p>${html(axiomAuditSummary(audit))}</p>
    <p class="audit-note">Dependencies of this proof, including theorem and definition certificates. This does not claim that these axioms are logically necessary.</p>
    <h3>Named axioms</h3>${audit.axioms.length ? audit.axioms.map(item => `<details class="audit-item"><summary><code>${html(item.name)}</code><span>${item.direct ? "Direct" : "Inherited"}</span></summary><pre>${html(item.statement)}</pre><ol>${item.path.map(step => `<li><code>${html(step)}</code></li>`).join("")}</ol></details>`).join("") : `<p>${audit.complete ? "No named axioms occur in this proof or its dependencies." : "No named axioms found in the available proofs."}</p>`}
    ${audit.unavailable.length ? `<h3>Unavailable proof dependencies</h3><ul>${audit.unavailable.map(item => `<li>${html(item.path.join(" → "))}</li>`).join("")}</ul>` : ""}
    <details class="audit-item"><summary>Definition and schema mechanisms <span>${audit.mechanisms.length}</span></summary><p>These built-in mechanisms are reported separately from named axioms. Unique description is not the axiom of Choice.</p><ul>${audit.mechanisms.map(item => `<li><code>${html(item.name)}</code> · ${html(item.kind)}</li>`).join("")}</ul></details>
    <p class="audit-note">Classical double-negation elimination: ${audit.classicalLogic ? "used" : "not used"}.</p>`;
}

/** Exact source keys prevent a hover from reusing an audit after an edit. */
export function createAxiomAuditLoader(request) {
  let workspace;
  const cache = new Map();
  return (theorem, payload) => {
    const key = JSON.stringify(payload);
    if (key !== workspace) { workspace = key; cache.clear(); }
    if (!cache.has(theorem)) {
      if (cache.size >= 128) cache.delete(cache.keys().next().value);
      const pending = request("axiom-audit", { ...payload, theorem }).then(audit => {
        if (!audit.ok) throw new Error(audit.message || "Audit unavailable");
        return audit;
      });
      cache.set(theorem, pending);
      pending.catch(() => { if (cache.get(theorem) === pending) cache.delete(theorem); });
    }
    return cache.get(theorem);
  };
}

// Keep the goal pane focused on proof development; offer auditing at QED only.
export function renderAxiomAuditAction(state, theorem, current = true) {
  if (!current || !theorem?.name || !Array.isArray(state?.goals) || state.goals.length) return "";
  return `<button type="button" class="qed-show qed-audit" data-axiom-audit="${html(theorem.name)}" title="Audit this theorem’s direct and inherited axioms" aria-label="Axiom audit for ${html(theorem.name)}">Axioms</button>`;
}
