// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The machine interface under a proof in progress: positions in a file that
// does not yet check, generated and out-of-scope declarations, header
// signatures, elaboration probes, batched audits, the command line's
// consistency, and the checker's --continue mode.

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { handleMachineRequest, MACHINE_PROTOCOL_VERSION, type MachineCheckResult } from "../src/machine-interface.ts";
import { parseDeclarationHeader, parseSearchQuery, scanSearchDeclarations } from "../src/library-search.ts";

const project = fileURLToPath(new URL("..", import.meta.url));

function g17(...args: string[]) {
  return spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", ...args], { cwd: project, encoding: "utf8" });
}

function ok<T = Record<string, any>>(response: ReturnType<typeof handleMachineRequest>): T {
  assert.equal(response.ok, true, JSON.stringify(response));
  assert.equal(response.version, MACHINE_PROTOCOL_VERSION);
  return (response as { result: T }).result;
}

function failed(response: ReturnType<typeof handleMachineRequest>): { code: string; message: string; [detail: string]: unknown } {
  assert.equal(response.ok, false, JSON.stringify(response));
  return (response as { error: { code: string; message: string } }).error;
}

// A theorem that checks, one whose third step fails, and one after it.
const pairSource = `module Pair
import Grace.Cumulus.Set.Core

theorem first.done (A B : Set)
  requires h : A ⊆ B
  shows A ⊆ B
proof
  exact h

theorem second.broken (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  unfold Subset
  intro x
  exact nonsense
  intro hx

theorem third.unchecked (A : Set)
  shows A ⊆ A
proof
  sorry
`;
const pair = [{ name: "Pair.g17", source: pairSource }];

// A section theorem in a file that does not check.
const sectionSource = `module Sec
import Grace.Cumulus.Set.Core

section Facts
variable (A B : Set)
hypothesis sub : A ⊆ B

theorem keep.sub (C : Set)
  requires more : B ⊆ C
  shows A ⊆ C
proof
  exact nonsense
end Facts
`;
const section = [{ name: "Sec.g17", source: sectionSource }];

test("a failed check still reports the theorems that completed before the failure", () => {
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 1, method: "check", params: { files: pair } }));
  assert.equal(result.status, "failed");
  assert.deepEqual(result.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status]),
    [["Pair.first.done", "proved"], ["Pair.second.broken", "failed"]]);
  const done = result.theorems[0]!;
  assert.equal(done.steps.length, 1);
  assert.equal(done.steps[0]!.command, "exact h");
  assert.equal(done.steps[0]!.after.goals.length, 0);
  assert.equal((done as { statement?: string }).statement, "∀ A, ∀ B, A ⊆ B → A ⊆ B");
  const [diagnostic] = result.diagnostics;
  assert.equal(diagnostic!.line, 17);
  assert.equal(diagnostic!.theorem, "Pair.second.broken");
});

test("goal answers from completed theorems and the partial trace, and names a position after the failure", () => {
  const before = ok(handleMachineRequest({ id: 2, method: "goal", params: { files: pair, line: 8, column: 1 } }));
  assert.equal(before.kind, "theorem");
  assert.equal(before.theorem, "Pair.first.done");
  assert.equal(before.theoremStatus, "proved");
  assert.equal(before.state.goals[0].goal, "A ⊆ B");
  const after = ok(handleMachineRequest({ id: 3, method: "goal", params: { files: pair, line: 8, column: 3 } }));
  assert.equal(after.complete, true);
  const atFailure = ok(handleMachineRequest({ id: 4, method: "goal", params: { files: pair, line: 17, column: 1 } }));
  assert.equal(atFailure.theorem, "Pair.second.broken");
  assert.equal(atFailure.caption, "Current goal, after line 16");
  assert.equal(atFailure.state.goals[0].goal, "x ∈ A → x ∈ C");
  assert.equal(atFailure.code, undefined);
  const beyond = ok(handleMachineRequest({ id: 5, method: "goal", params: { files: pair, line: 18, column: 1 } }));
  assert.equal(beyond.kind, "theorem");
  assert.equal(beyond.code, "after_failure");
  assert.equal(beyond.caption, "After the failure at line 17");
  assert.equal(beyond.state.goals[0].goal, "x ∈ A → x ∈ C");
  assert.match(beyond.message, /after the failure at line 17/);
  const later = ok(handleMachineRequest({ id: 6, method: "goal", params: { files: pair, line: 21, column: 1 } }));
  assert.equal(later.kind, "none");
  assert.equal(later.code, "after_failure");
  assert.equal(later.diagnostic.line, 17);
});

test("suggest runs in a completed theorem of a failing file and refuses positions after the failure", () => {
  const result = ok(handleMachineRequest({ id: 7, method: "suggest", params: { files: pair, line: 8, column: 1, tactic: "exact?" } }));
  assert.equal(result.theorem, "Pair.first.done");
  assert.deepEqual(result.inserted, { line: 8, text: "  exact?" });
  assert.equal(result.goal.goals[0].goal, "A ⊆ B");
  assert.equal(result.suggestions[0].command, "exact h");
  assert.equal(result.suggestions[0].source, "local");
  const beyond = failed(handleMachineRequest({ id: 8, method: "suggest", params: { files: pair, line: 18, tactic: "exact?" } }));
  assert.equal(beyond.code, "after_failure");
  assert.equal(beyond.failureLine, 17);
  assert.equal(beyond.theorem, "Pair.second.broken");
  const later = failed(handleMachineRequest({ id: 9, method: "suggest", params: { files: pair, line: 22, tactic: "exact?" } }));
  assert.equal(later.code, "after_failure");
  // Before the failing step the query still runs at that state.
  const at = ok(handleMachineRequest({ id: 10, method: "suggest", params: { files: pair, line: 17, column: 1, tactic: "apply?" } }));
  assert.equal(at.goal.goals[0].goal, "x ∈ A → x ∈ C");
  // An unfinished proof is not a failed step: the line after its last step takes a tactic.
  const unfinished = [{ name: "Open.g17", source: pairSource.replace("  exact nonsense\n  intro hx\n", "  intro hx\n") }];
  const next = ok(handleMachineRequest({ id: 11, method: "goal", params: { files: unfinished, line: 18, column: 1 } }));
  assert.equal(next.code, undefined);
  assert.equal(next.state.goals[0].goal, "x ∈ C");
});

test("declaration resolves generated facts and names the module of a declaration outside the closure", () => {
  const generated = ok(handleMachineRequest({ id: 12, method: "declaration", params: { name: "Bool.inductive.disjoint.false.true" } }));
  assert.equal(generated.elaborated, true);
  assert.equal(generated.generated, true);
  assert.equal(generated.kind, "property");
  assert.equal(generated.name, "Grace.Core.Data.Bool.inductive.disjoint.false.true");
  assert.equal(generated.definition, "Grace.Core.Data.Bool.inductive");
  assert.match(generated.statement, /false|true/);
  assert.equal(generated.module, "Grace.Core.Data");
  const outside = ok(handleMachineRequest({ id: 13, method: "declaration", params: { name: "GroupHom.map_mem", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(outside.elaborated, false);
  assert.equal(outside.inScope, false);
  assert.equal(outside.import, "Grace.Cumulus.Algebra.Group.Homomorphism");
  assert.equal(outside.kind, "instance");
  assert.match(outside.message, /import Grace\.Cumulus\.Algebra\.Group\.Homomorphism/);
  const instance = ok(handleMachineRequest({ id: 14, method: "declaration", params: { name: "GroupHom.map_mem" } }));
  assert.equal(instance.kind, "instance");
});

test("signature reads parameters, premises, and the positional at/with lists from the header, even in a failing file", () => {
  const library = ok(handleMachineRequest({ id: 15, method: "signature", params: { name: "Subset.transitive" } }));
  assert.equal(library.name, "Grace.Cumulus.Set.Core.Subset.transitive");
  assert.deepEqual(library.parameters.map((item: { name: string; type: string; binder: string }) => [item.name, item.type, item.binder]),
    [["A", "Set", "explicit"], ["B", "Set", "explicit"], ["C", "Set", "explicit"]]);
  assert.deepEqual(library.premises.map((item: { name: string; formula: string }) => [item.name, item.formula]), [["hAB", "A ⊆ B"], ["hBC", "B ⊆ C"]]);
  assert.deepEqual(library.positional, { at: ["A", "B", "C"], with: ["hAB", "hBC"] });
  assert.equal(library.elaborated, false);
  const inSection = ok(handleMachineRequest({ id: 16, method: "signature", params: { name: "keep.sub", files: section, elaborate: true } }));
  assert.equal(inSection.name, "Sec.keep.sub");
  assert.deepEqual(inSection.parameters.map((item: { name: string; source: string }) => [item.name, item.source]),
    [["A", "section"], ["B", "section"], ["C", "declaration"]]);
  assert.deepEqual(inSection.premises.map((item: { name: string; source: string }) => [item.name, item.source]),
    [["sub", "section"], ["more", "declaration"]]);
  assert.deepEqual(inSection.positional, { at: ["A", "B", "C"], with: ["sub", "more"] });
  assert.equal(inSection.conclusion, "A ⊆ C");
  assert.equal(inSection.elaborated, false);
  assert.equal(inSection.checkFailed.line, 12);
  const elaborated = ok(handleMachineRequest({ id: 17, method: "signature", params: { name: "Subset.transitive", module: "Grace.Cumulus.Set.Core", elaborate: true } }));
  assert.equal(elaborated.elaborated, true);
  assert.equal(elaborated.statement, "∀ A, ∀ B, ∀ C, A ⊆ B → B ⊆ C → A ⊆ C");
  const header = parseDeclarationHeader({ kind: "theorem", short: "length.closed", signature: "theorem length.closed {A : Set} (xs : List(A))\nshows Nat(length(xs))", context: "" });
  assert.deepEqual(header.parameters.map(item => [item.name, item.type, item.binder]), [["A", "Set", "implicit"], ["xs", "List(A)", "explicit"]]);
  assert.equal(header.conclusion, "Nat(length(xs))");
  const grouped = parseDeclarationHeader({ kind: "theorem", short: "sum.succ", signature: "theorem sum.succ (u : Set, n : Nat) (a b ∈ O)\nshows u = u", context: "" });
  assert.deepEqual(grouped.parameters.map(item => [item.name, item.type]), [["u", "Set"], ["n", "Nat"], ["a", "∈ O"], ["b", "∈ O"]]);
  assert.equal(failed(handleMachineRequest({ id: 18, method: "signature", params: { name: "No.Such.Thing" } })).code, "unknown_declaration");
});

test("elaborate prints a written formula or term in its kernel form with resolved names", () => {
  const formula = ok(handleMachineRequest({ id: 19, method: "elaborate", params: { text: "A ⊆ B", variables: "(A B : Set)", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(formula.kind, "formula");
  assert.equal(formula.printed, "A ⊆ B");
  assert.equal(typeof formula.canonical, "string");
  assert.equal(formula.symbols.length, 1);
  assert.match(formula.symbols[0].name, /\.Subset$/);
  assert.equal(formula.symbols[0].kind, "definition");
  const term = ok(handleMachineRequest({ id: 20, method: "elaborate", params: { text: "pair(A, B)", variables: "(A B : Set)", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(term.kind, "term");
  assert.equal(term.printed, "{A, B}");
  assert.match(term.canonical, /pair\(A, B\)$|^\{A, B\}$/);
  // In a file, at a line: the section variables are in scope there, and the
  // file need not check.
  const inFile = ok(handleMachineRequest({ id: 21, method: "elaborate", params: { text: "A ⊆ B ∧ B ⊆ A", files: section, line: 10 } }));
  assert.equal(inFile.file, "Sec.g17");
  assert.equal(inFile.line, 8);
  assert.equal(inFile.printed, "A ⊆ B ∧ B ⊆ A");
  const bad = failed(handleMachineRequest({ id: 22, method: "elaborate", params: { text: "A ⊆", variables: "(A : Set)", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(bad.code, "elaboration_failed");
});

test("audit takes several theorems over one environment and pin reports its state", () => {
  const files = [{ name: "Probe.g17", source: pairSource.replace("  exact nonsense\n  intro hx\n", "  intro hx\n  exact second with x, (first with x, hx)\n") }];
  const audits = ok(handleMachineRequest({ id: 23, method: "audit", params: { files, theorems: ["Pair.first.done", "Pair.third.unchecked"] } }));
  assert.equal(audits.audits.length, 2);
  assert.deepEqual(audits.audits[0].hereditary, []);
  assert.deepEqual(audits.audits[1].direct, ["sorry.Pair.third.unchecked.23.1"]);
  assert.equal(ok(handleMachineRequest({ id: 24, method: "pin", params: { enabled: true } })).pinned, true);
  assert.equal(ok(handleMachineRequest({ id: 25, method: "capabilities" })).pinned, true);
  assert.equal(ok(handleMachineRequest({ id: 26, method: "pin", params: { enabled: false } })).pinned, false);
  assert.equal(ok(handleMachineRequest({ id: 27, method: "capabilities" })).pinned, undefined);
});

test("search accepts a symbol after a field colon and the command line is consistent", () => {
  assert.deepEqual(parseSearchQuery("conclusion: ∈ ω").map(item => [item.field, item.value]), [["conclusion", "∈ ω"]]);
  assert.deepEqual(parseSearchQuery("conclusion: _ = 0 ∨ _ = 0 -module:Core").map(item => [item.field, item.value, item.exclude]),
    [["conclusion", "_ = 0 ∨ _ = 0", false], ["module", "core", true]]);
  assert.deepEqual(parseSearchQuery("name: foo bar").map(item => [item.field, item.value]), [["name", "foo"], ["text", "bar"]]);
  const search = g17("search", "conclusion: ∈ ω", "--limit", "1");
  assert.equal(search.status, 0, search.stderr);
  assert.equal(JSON.parse(search.stdout).result.total > 0, true);
  const help = g17("check", "--help");
  assert.equal(help.status, 0, help.stderr);
  assert.match(help.stdout, /^usage:/);
  const goal = g17("goal", "--module-root", "lib", "--line", "8", "--text", "examples/Sets.g17");
  assert.equal(goal.status, 0, goal.stderr);
  assert.doesNotThrow(() => { if (goal.stdout.startsWith("{")) throw new Error("text expected"); });
  const directory = mkdtempSync(join(tmpdir(), "g17-cli-"));
  try {
    const broken = join(directory, "Pair.g17");
    writeFileSync(broken, pairSource);
    const json = g17("check", "--json", "--module-root", "lib", broken);
    assert.equal(json.status, 1);
    // The failure JSON is on standard output, where a redirection finds it.
    assert.equal(json.stderr, "");
    const failure = JSON.parse(json.stdout);
    assert.equal(failure.ok, false);
    assert.equal(failure.status, "failed");
    assert.equal(typeof failure.milliseconds, "number");
    assert.equal(failure.diagnostics[0].theorem, "Pair.second.broken");
    assert.equal(failure.diagnostics[0].file, broken);
    assert.equal(failure.theorems[0].name, "Pair.first.done");
    const text = g17("check", "--module-root", "lib", broken);
    assert.equal(text.status, 1);
    assert.match(text.stderr, new RegExp(`surface error in .*Pair\\.g17: line 17`));
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("check --continue goes past a failing module, skips its dependents, and reports every failure", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-continue-"));
  const write = (name: string, body: string) => writeFileSync(join(directory, `${name}.g17`), body);
  try {
    write("A", "module A\n\ntheorem a.refl (x : Set)\n  shows x = x\nproof\n  rfl\n");
    write("B", "module B\nimport A\n\ntheorem b.broken (x : Set)\n  shows x = x\nproof\n  exact nonsense\n");
    write("C", "module C\nimport B\n\ntheorem c.refl (x : Set)\n  shows x = x\nproof\n  rfl\n");
    write("D", "module D\n\ntheorem d.refl (x : Set)\n  shows x = x\nproof\n  rfl\n");
    write("Root", "module Root\nimport C\nimport D\n");
    const text = g17("check", "--continue", "--module-root", directory, join(directory, "Root.g17"));
    assert.equal(text.status, 1, text.stdout + text.stderr);
    assert.match(text.stdout, /checked .*A\.g17/);
    assert.match(text.stdout, /checked .*D\.g17/);
    assert.match(text.stdout, /failed .*B\.g17 \[B\]: surface error/);
    assert.match(text.stdout, /skipped .*C\.g17 \[C\]: imports B/);
    assert.match(text.stdout, /skipped .*Root\.g17 \[Root\]: imports C/);
    assert.match(text.stdout, /2 modules checked, 1 failed, 2 skipped/);
    const json = g17("check", "--json", "--continue", "--module-root", directory, join(directory, "Root.g17"));
    assert.equal(json.status, 1, json.stderr);
    const result = JSON.parse(json.stdout);
    assert.equal(result.ok, false);
    assert.equal(result.status, "failed");
    assert.deepEqual(result.failures.map((item: { module: string; line: number }) => [item.module, item.line]), [["B", 7]]);
    assert.deepEqual(result.skipped.map((item: { module: string; because: string }) => [item.module, item.because]), [["C", "B"], ["Root", "C"]]);
    assert.equal(result.diagnostics[0].theorem, "B.b.broken");
    assert.ok(result.checked.some((item: { module?: string }) => item.module === "D"));
    const good = g17("check", "--continue", "--module-root", directory, join(directory, "D.g17"));
    assert.equal(good.status, 0, good.stderr);
    assert.match(good.stdout, /1 modules checked, 0 failed, 0 skipped/);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("the search index scans instances and the header parser reads section context", () => {
  const records = scanSearchDeclarations("Sec.g17", sectionSource);
  assert.deepEqual(records.map(item => [item.kind, item.name]), [["theorem", "keep.sub"]]);
  assert.equal(records[0]!.context, "variable (A B : Set)\nhypothesis sub : A ⊆ B");
});

// A defgraph whose codomain proof is a traced proof block, like a theorem's.
const graphSource = `module Graph
import Grace.Cumulus.Set.Function

theorem first.done (A B : Set)
  requires h : A ⊆ B
  shows A ⊆ B
proof
  exact h

defgraph ident (A : Set) (x ∈ A) : A := x
proof
  have again : x ∈ A := member
  exact again

theorem later (A : Set)
  shows A ⊆ A
proof
  sorry
`;

test("goal answers inside a defgraph's codomain proof, in a checked file and at the failing step", () => {
  const checked = [{ name: "Graph.g17", source: graphSource }];
  const inside = ok(handleMachineRequest({ id: 40, method: "goal", params: { files: checked, line: 13, column: 1 } }));
  assert.equal(inside.kind, "theorem");
  assert.equal(inside.theorem, "Graph.ident.closed");
  assert.equal(inside.caption, "Current goal, after line 12");
  assert.equal(inside.state.goals[0].locals.at(-1).name, "again");
  assert.equal(inside.lineStart, 10);
  assert.equal(inside.lineEnd, 13);
  const end = ok(handleMachineRequest({ id: 41, method: "goal", params: { files: checked, line: 13, column: 20 } }));
  assert.equal(end.complete, true);
  const signature = ok(handleMachineRequest({ id: 42, method: "signature", params: { name: "ident.value", files: checked } }));
  assert.equal(signature.generated, true);
  assert.equal(signature.name, "Graph.ident.value");
  assert.equal(signature.definition, "Graph.ident");
  assert.deepEqual(signature.parameters.map((item: { name: string }) => item.name), ["A", "x"]);
  assert.deepEqual(signature.premises.map((item: { formula: string }) => item.formula), ["x ∈ A"]);
  assert.equal(signature.conclusion, "ident(A)(x) = x");
  assert.equal(signature.elaborated, true);
  const closed = ok(handleMachineRequest({ id: 43, method: "declaration", params: { name: "ident.closed", files: checked } }));
  assert.equal(closed.name, "Graph.ident.closed");
  assert.equal(closed.kind, "theorem");
  // The step that fails is inside the definition's proof: the trace is
  // located at the definition, not collapsed to the failing line.
  const failing = [{ name: "Graph.g17", source: graphSource.replace("  exact again\n", "  exact nonsense\n") }];
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 44, method: "check", params: { files: failing } }));
  assert.deepEqual(result.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status, theorem.lineStart, theorem.lineEnd]),
    [["Graph.first.done", "proved", 4, 9], ["Graph.ident.closed", "failed", 10, 14]]);
  const before = ok(handleMachineRequest({ id: 45, method: "goal", params: { files: failing, line: 12, column: 1 } }));
  assert.equal(before.kind, "theorem");
  assert.equal(before.theorem, "Graph.ident.closed");
  assert.equal(before.step, 0);
  const at = ok(handleMachineRequest({ id: 46, method: "goal", params: { files: failing, line: 13, column: 1 } }));
  assert.equal(at.caption, "Current goal, after line 12");
  assert.equal(failed(handleMachineRequest({ id: 47, method: "suggest", params: { files: failing, line: 14, tactic: "exact?" } })).code, "after_failure");
  // A defgraph that completed before a later failure is still reported.
  const later = [{ name: "Graph.g17", source: graphSource.replace("  sorry\n", "  exact nonsense\n") }];
  const partial = ok<MachineCheckResult>(handleMachineRequest({ id: 48, method: "check", params: { files: later } }));
  assert.deepEqual(partial.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status]),
    [["Graph.first.done", "proved"], ["Graph.ident.closed", "proved"], ["Graph.later", "failed"]]);
});

test("audit with several theorems answers one entry per name, an error entry for a name not found", () => {
  const files = [{ name: "Graph.g17", source: graphSource }];
  const result = ok(handleMachineRequest({ id: 50, method: "audit", params: { files, theorems: ["Graph.first.done", "Graph.missing", "Graph.later"] } }));
  assert.equal(result.audits.length, 3);
  assert.equal(result.audits[0].theorem, "Graph.first.done");
  assert.equal(result.audits[0].complete, true);
  assert.deepEqual(result.audits[1], { theorem: "Graph.missing", error: { code: "unknown_theorem", message: "Unknown theorem: Graph.missing" } });
  assert.deepEqual(result.audits[2].direct, ["sorry.Graph.later.18.1"]);
  const directory = mkdtempSync(join(tmpdir(), "g17-audit-"));
  try {
    const file = join(directory, "Graph.g17");
    writeFileSync(file, graphSource);
    const cli = g17("audit", "--module-root", "lib", file, "--theorem", "Graph.first.done", "--theorem", "Nope.missing");
    assert.equal(cli.status, 0, cli.stderr);
    const printed = JSON.parse(cli.stdout);
    assert.deepEqual(printed.result.audits.map((item: { theorem: string; error?: { code: string } }) => [item.theorem, item.error?.code]),
      [["Graph.first.done", undefined], ["Nope.missing", "unknown_theorem"]]);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("search matches wildcard conclusions and name pieces, and ranks the exact conclusion shape first", () => {
  const zero = ok(handleMachineRequest({ id: 60, method: "search", params: { query: "conclusion: _ = 0 ∨ _ = 0" } }));
  assert.ok(zero.results.some((item: { name: string }) => item.name === "mul.eq_zero_iff"), JSON.stringify(zero.results.map((item: { name: string }) => item.name)));
  assert.ok(zero.results.every((item: { conclusion: string }) => item.conclusion.includes("∨")));
  const pieces = ok(handleMachineRequest({ id: 61, method: "search", params: { query: "name:mul_eq_zero" } }));
  assert.ok(pieces.results.some((item: { name: string }) => item.name === "mul.eq_zero_iff"));
  assert.ok(pieces.results.some((item: { name: string }) => item.name === "realMulValue.square_eq_zero_iff"));
  const shape = ok(handleMachineRequest({ id: 62, method: "search", params: { query: "conclusion: A ∖ B ⊆ A", limit: 3 } }));
  assert.equal(shape.results[0].name, "difference.subset_left");
  const quoted = ok(handleMachineRequest({ id: 63, method: "search", params: { query: 'conclusion:"A ⊆ C" module:Set.Core' } }));
  assert.equal(quoted.results[0].name, "Subset.transitive");
});

test("declaration and signature take a module to pick among same-named declarations and list candidates with modules", () => {
  const error = failed(handleMachineRequest({ id: 70, method: "declaration", params: { name: "orderedPair.injective" } }));
  assert.equal(error.code, "ambiguous_name");
  const declarations = error.declarations as { name: string; module: string }[];
  assert.ok(declarations.some(item => item.name === "Grace.Cumulus.Set.Relation.orderedPair.injective" && item.module === "Grace.Cumulus.Set.Relation"));
  assert.equal(declarations.length, (error.candidates as string[]).length);
  const chosen = ok(handleMachineRequest({ id: 71, method: "declaration", params: { name: "orderedPair.injective", module: "Grace.Cumulus.Set.Relation" } }));
  assert.equal(chosen.name, "Grace.Cumulus.Set.Relation.orderedPair.injective");
  assert.equal(chosen.elaborated, true);
  const own = ok(handleMachineRequest({ id: 72, method: "signature", params: { name: "one_mul", module: "Grace.Cumulus.Algebra.Group.Basic" } }));
  assert.equal(own.name, "Grace.Cumulus.Algebra.Group.Basic.one_mul");
  assert.equal(failed(handleMachineRequest({ id: 73, method: "signature", params: { name: "one_mul" } })).code, "ambiguous_name");
  // A generated fact of a definition outside the environment names the module to import.
  const outside = ok(handleMachineRequest({ id: 74, method: "declaration", params: { name: "inclusionMap.value", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(outside.inScope, false);
  assert.equal(outside.import, "Grace.Cumulus.Set.Inclusion");
  assert.equal(outside.name, "Grace.Cumulus.Set.Inclusion.inclusionMap.value");
  assert.equal(typeof outside.statement, "string");
  const generated = ok(handleMachineRequest({ id: 75, method: "signature", params: { name: "inclusionMap.closed" } }));
  assert.equal(generated.generated, true);
  assert.equal(generated.module, "Grace.Cumulus.Set.Inclusion");
  assert.deepEqual(generated.parameters.map((item: { name: string }) => item.name), ["A", "B", "x"]);
  assert.deepEqual(generated.premises.map((item: { formula: string }) => item.formula), ["A ⊆ B", "x ∈ A"]);
  assert.equal(generated.conclusion, "x ∈ B");
});
