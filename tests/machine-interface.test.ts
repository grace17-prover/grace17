// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { callMachineMethod, handleMachineRequest, MACHINE_METHODS, MACHINE_PROTOCOL_VERSION, type MachineCheckResult } from "../src/machine-interface.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { LibrarySearchIndex, scanSearchDeclarations } from "../src/library-search.ts";
import { tacticStepAtCursor, resolveSymbolCandidate } from "../src/workbench-navigation.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const example = (name: string) => ({ name: join(project, "examples", name), source: readFileSync(join(project, "examples", name), "utf8") });
const core = join(project, "lib/Grace/Cumulus/Set/Core.g17");

const imageSource = `module Probe
import Grace.Cumulus.Set.Function

theorem image_in (f X A B k : Set)
  requires fFunction : f : A → B
  requires inA : ∀ k ∈ A, X(k) ∈ A
  requires hk : k ∈ A
  shows f(X(k)) ∈ B
proof
  sorry
`;

const brokenSource = `module Broken
import Grace.Cumulus.Set.Core

theorem subset_chain (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  unfold Subset
  intro x
  intro hx
`;

function ok<T = Record<string, any>>(response: ReturnType<typeof handleMachineRequest>): T {
  assert.equal(response.ok, true, JSON.stringify(response));
  assert.equal(response.version, MACHINE_PROTOCOL_VERSION);
  return (response as { result: T }).result;
}

function failed(response: ReturnType<typeof handleMachineRequest>): { code: string; message: string; [detail: string]: unknown } {
  assert.equal(response.ok, false, JSON.stringify(response));
  assert.equal(response.version, MACHINE_PROTOCOL_VERSION);
  return (response as { error: { code: string; message: string } }).error;
}

test("capabilities lists every method with the protocol version", () => {
  const result = ok(handleMachineRequest({ id: 1, method: "capabilities" }));
  assert.equal(result.protocol, MACHINE_PROTOCOL_VERSION);
  assert.deepEqual(result.methods.map((item: { name: string }) => item.name),
    ["capabilities", "check", "goal", "suggest", "search", "declaration", "signature", "elaborate", "audit", "library", "notations", "pin", "closure"]);
  assert.equal(result.methods.length, MACHINE_METHODS.length);
  assert.deepEqual(result.foundations, ["ZF", "ZFC", "ZFG"]);
});

test("check reports every theorem of an example file with the Workbench's printed states", () => {
  const file = example("Sets.g17");
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 2, method: "check", params: { files: [file] } }));
  assert.equal(result.status, "checked");
  assert.equal(result.foundation.profile, "ZFG");
  assert.ok(result.theorems.length >= 7);
  assert.ok(result.theorems.every(theorem => theorem.status === "proved"));
  assert.deepEqual(result.diagnostics, []);
  assert.equal(result.files[0]!.status, "checked");
  assert.ok(result.checked.some(item => item.file === file.name));
  const first = result.theorems[0]!;
  assert.equal(first.name, "pair.left");
  assert.ok(first.steps.length > 0 && first.initial);
  assert.ok(first.dependencies.axioms.length > 0, "dependencies are reported by default");
  // Character for character what checkWorkbenchFiles returns for the same file.
  const workbench = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false, includeEnvironmentDigest: false });
  assert.deepEqual(result.theorems.map(theorem => [theorem.name, theorem.statement, theorem.initial, theorem.steps]),
    workbench.theorems.map(theorem => [theorem.name, theorem.statement, theorem.initial, theorem.steps]));
});

test("check accepts a library module by path and audits each theorem on request", () => {
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 3, method: "check", params: { files: [{ name: core }], audit: true } }));
  assert.equal(result.status, "checked");
  assert.equal(result.files[0]!.module, "Grace.Cumulus.Set.Core");
  const transitive = result.theorems.find(theorem => theorem.name === "Grace.Cumulus.Set.Core.Subset.transitive")!;
  assert.ok(transitive);
  assert.equal(transitive.status, "proved");
  const audit = (transitive as { audit?: { complete: boolean; hereditary: string[] } }).audit!;
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.hereditary, []);
  assert.ok(result.checked.some(item => item.module === "Grace.Cumulus.Set.Core"));
});

test("a failing proof yields a diagnostic with position and the partial trace", () => {
  const files = [{ name: "Broken.g17", source: brokenSource }];
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 4, method: "check", params: { files } }));
  assert.equal(result.status, "failed");
  assert.equal(result.diagnostics.length, 1);
  const [diagnostic] = result.diagnostics;
  assert.equal(diagnostic!.file, "Broken.g17");
  assert.equal(diagnostic!.line, 11);
  assert.equal(diagnostic!.column, 1);
  assert.equal(diagnostic!.severity, "error");
  assert.match(diagnostic!.message, /1 goal remains; next is x ∈ C/);
  assert.equal(diagnostic!.theorem, "Broken.subset_chain");
  const [theorem] = result.theorems;
  assert.equal(theorem!.status, "failed");
  assert.equal((theorem as { name?: string }).name, "Broken.subset_chain");
  assert.equal(theorem!.steps.length, 3);
  assert.deepEqual(theorem!.steps.at(-1)!.after.goals[0]!.locals.map(local => local.name), ["first", "second", "hx"]);
  assert.equal(theorem!.steps.at(-1)!.after.goals[0]!.goal, "x ∈ C");
  assert.equal(result.files[0]!.status, "failed");
});

test("goal returns the state the Workbench shows at a position", () => {
  const files = [{ name: "Broken.g17", source: brokenSource }];
  const start = ok(handleMachineRequest({ id: 5, method: "goal", params: { files, line: 9, column: 1 } }));
  assert.equal(start.kind, "theorem");
  assert.equal(start.theorem, "Broken.subset_chain");
  assert.equal(start.step, 0);
  assert.equal(start.caption, "Current goal, at theorem start");
  assert.equal(start.state.goals[0].goal, "A ⊆ C");
  const after = ok(handleMachineRequest({ id: 6, method: "goal", params: { files, line: 10, column: 3 } }));
  assert.equal(after.step, 2);
  assert.equal(after.command, "intro x");
  assert.equal(after.caption, "Current goal, after line 10");
  assert.equal(after.state.goals[0].goal, "x ∈ A → x ∈ C");
  const end = ok(handleMachineRequest({ id: 7, method: "goal", params: { files, line: 11, column: 20 } }));
  assert.equal(end.caption, "Current position, after line 11");
  assert.equal(end.diagnostic.line, 11);
  const outside = ok(handleMachineRequest({ id: 8, method: "goal", params: { files, line: 2, column: 1 } }));
  assert.equal(outside.kind, "none");
  assert.equal(tacticStepAtCursor([{ line: 9, columnStart: 3 }, { line: 10, columnStart: 3 }], 10, 1), 1);
});

test("suggest runs exact? at a position, returns structured suggestions, and the first one pastes and checks", () => {
  const files = [{ name: "Probe.g17", source: imageSource }];
  const result = ok(handleMachineRequest({ id: 9, method: "suggest", params: { files, line: 10, tactic: "exact?" } }));
  assert.equal(result.tactic, "exact?");
  assert.equal(result.theorem, "Probe.image_in");
  assert.deepEqual(result.inserted, { line: 10, text: "  exact?" });
  assert.equal(result.goal.goals[0].goal, "f(Xₖ) ∈ B");
  const [first] = result.suggestions;
  assert.equal(first.command, "exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)");
  assert.equal(first.name, "Grace.Cumulus.Set.Function.FunctionBetween.apply_closed");
  assert.equal(first.reference, "FunctionBetween.apply_closed");
  assert.equal(first.source, "theorem");
  assert.deepEqual(first.arguments, ["f", "A", "B", "Xₖ"]);
  assert.deepEqual(first.premises.map((premise: { formula: string; evidence: string }) => [premise.formula, premise.evidence]),
    [["f : A → B", "fFunction"], ["Xₖ ∈ A", "(inA at k with hk)"]]);
  assert.equal(first.closes, true);
  assert.deepEqual(result.items, result.suggestions.map((item: { command: string }) => item.command));
  assert.equal(result.after.goals.length, 0);
  // Results only reachable by their full name (the _root_ form) are offered
  // only when nothing the module can name closes the goal; here one does.
  assert.ok(result.suggestions.every((item: { reference: string }) => !item.reference.startsWith("_root_.")), "no _root_ suggestion beside a reachable one");
  assert.ok(result.suggestions[0].command.startsWith(`exact ${result.suggestions[0].reference}`));
  // Paste the suggestion over the sorry and the file checks without admissions.
  const pasted = imageSource.replace("  sorry", `  ${first.command}`);
  const checked = ok<MachineCheckResult>(handleMachineRequest({ id: 10, method: "check", params: { files: [{ name: "Probe.g17", source: pasted }] } }));
  assert.equal(checked.status, "checked");
  assert.equal(checked.theorems[0]!.status, "proved");
  assert.deepEqual(checked.diagnostics, []);
  // The original file is untouched: it still has its sorry.
  const original = ok<MachineCheckResult>(handleMachineRequest({ id: 11, method: "check", params: { files } }));
  assert.equal(original.theorems[0]!.status, "admitted");
  assert.equal(original.diagnostics[0]!.severity, "warning");
});

test("suggest ranks rw? results with the closing rewrites first", () => {
  const source = `module Rewrite
import Grace.Cumulus.Set.Core

theorem found.rewrite (x y : Set)
  requires h : x = y
  shows pair(x, x) = pair(y, y)
proof
  sorry
`;
  const result = ok(handleMachineRequest({ id: 12, method: "suggest", params: { files: [{ name: "Rewrite.g17", source }], line: 8, tactic: "rw" } }));
  assert.equal(result.tactic, "rw?");
  assert.equal(result.suggestions[0].command, "rw h");
  assert.equal(result.suggestions[0].source, "local");
  assert.equal(result.suggestions[0].closes, true);
  assert.equal(result.suggestions[0].reverse, false);
  assert.equal(result.suggestions[0].goal, "{y, y} = {y, y}");
  const closing = result.suggestions.filter((item: { closes: boolean }) => item.closes).length;
  assert.ok(closing >= 1 && closing < result.suggestions.length);
  assert.ok(result.suggestions.slice(0, closing).every((item: { closes: boolean }) => item.closes));
  assert.ok(result.suggestions.slice(closing).every((item: { closes: boolean }) => !item.closes));
  // A failed search is a result, not an error.
  const none = ok(handleMachineRequest({ id: 13, method: "suggest", params: { files: [{ name: "Broken.g17", source: brokenSource }], line: 12, tactic: "rw?" } }));
  assert.deepEqual(none.suggestions, []);
  assert.match(none.message, /rw\? found no rewrite rule/);
});

test("search uses the Workbench query language over the library and open files", () => {
  const result = ok(handleMachineRequest({ id: 14, method: "search", params: { query: "name:transitive module:Set.Core" } }));
  assert.equal(result.total, 1);
  const [hit] = result.results;
  assert.equal(hit.name, "Subset.transitive");
  assert.equal(hit.kind, "theorem");
  assert.equal(hit.module, "Grace.Cumulus.Set.Core");
  assert.equal(hit.file, "lib/Grace/Cumulus/Set/Core.g17");
  assert.equal(hit.line, 15);
  assert.match(hit.signature, /^theorem Subset\.transitive/);
  assert.equal(hit.conclusion, "(A ⊆ C)");
  const index = new LibrarySearchIndex();
  index.updateFile("lib/Grace/Cumulus/Set/Core.g17", readFileSync(core, "utf8"));
  assert.deepEqual(index.search("name:transitive").results.map(item => item.line), result.results.map((item: { line: number }) => item.line));
  const open = ok(handleMachineRequest({ id: 15, method: "search", params: { query: "image_in", files: [{ name: "Probe.g17", source: imageSource }] } }));
  assert.equal(open.results[0].file, "Probe.g17");
  assert.equal(failed(handleMachineRequest({ id: 16, method: "search", params: { query: "wat:x" } })).code, "bad_query");
});

test("declaration reports what the hover shows, in an environment or from the library source", () => {
  const elaborated = ok(handleMachineRequest({ id: 17, method: "declaration", params: { name: "Subset.transitive", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal(elaborated.elaborated, true);
  assert.equal(elaborated.name, "Grace.Cumulus.Set.Core.Subset.transitive");
  assert.equal(elaborated.kind, "theorem");
  assert.equal(elaborated.statement, "∀ A, ∀ B, ∀ C, A ⊆ B → B ⊆ C → A ⊆ C");
  assert.equal(elaborated.info, elaborated.statement);
  assert.equal(elaborated.file, core);
  assert.equal(elaborated.line, 15);
  assert.equal(elaborated.module, "Grace.Cumulus.Set.Core");
  const source = ok(handleMachineRequest({ id: 18, method: "declaration", params: { name: "Grace.Cumulus.Set.Core.Subset.transitive" } }));
  assert.equal(source.elaborated, false);
  assert.equal(source.line, 15);
  assert.equal(source.module, "Grace.Cumulus.Set.Core");
  assert.match(source.signature, /shows \(A ⊆ C\)/);
  assert.equal(failed(handleMachineRequest({ id: 19, method: "declaration", params: { name: "No.Such.Declaration" } })).code, "unknown_declaration");
  const symbols = [{ name: "A.b", short: "b", kind: "theorem", info: "" }, { name: "C.b", short: "b", kind: "theorem", info: "", file: "C.g17" }];
  assert.equal(resolveSymbolCandidate(symbols, "b", { file: "C.g17" })?.name, "C.b");
});

test("audit reports direct and inherited axioms, sorry admissions included", () => {
  const result = ok(handleMachineRequest({ id: 20, method: "audit", params: { files: [{ name: "Probe.g17", source: imageSource }], theorem: "Probe.image_in" } }));
  assert.equal(result.complete, true);
  assert.deepEqual(result.direct, ["sorry.Probe.image_in.10.1"]);
  assert.deepEqual(result.hereditary, ["sorry.Probe.image_in.10.1"]);
  assert.equal(result.axioms[0].direct, true);
  assert.equal(failed(handleMachineRequest({ id: 21, method: "audit", params: { files: [{ name: "Probe.g17", source: imageSource }], theorem: "Probe.missing" } })).code, "unknown_theorem");
});

test("library lists modules by area with their declarations", () => {
  const result = ok(handleMachineRequest({ id: 22, method: "library", params: { area: "Set" } }));
  assert.equal(result.areas[0].name, "Set");
  const module = result.modules.find((item: { module: string }) => item.module === "Grace.Cumulus.Set.Core");
  assert.ok(module);
  assert.equal(module.file, "lib/Grace/Cumulus/Set/Core.g17");
  assert.ok(module.declarations.some((item: { name: string; line: number }) => item.name === "Subset.transitive" && item.line === 15));
  assert.equal(module.declarationCount, scanSearchDeclarations(module.file, readFileSync(core, "utf8")).length);
  const all = ok(handleMachineRequest({ id: 23, method: "library" }));
  assert.ok(all.areas.some((item: { name: string }) => item.name === "Real"));
  assert.ok(all.modules.every((item: { declarations?: unknown }) => item.declarations === undefined));
  assert.equal(failed(handleMachineRequest({ id: 24, method: "library", params: { module: "Grace.Nowhere" } })).code, "unknown_module");
});

test("notations lists the notation table in scope for a module", () => {
  const result = ok(handleMachineRequest({ id: 25, method: "notations", params: { module: "Grace.Cumulus.Set.Core" } }));
  const subset = result.notations.find((item: { token: string }) => item.token === "⊆");
  assert.ok(subset);
  assert.equal(subset.kind, "predicate");
  assert.match(subset.target, /Subset$/);
  assert.ok(Array.isArray(result.tactics));
});

test("protocol errors carry a code and a message, never a stack", () => {
  assert.equal(failed(handleMachineRequest({ id: 26, method: "nope" })).code, "unknown_method");
  assert.equal(failed(handleMachineRequest({ id: 27, method: "check" })).code, "invalid_params");
  assert.equal(failed(handleMachineRequest({ id: 28, method: "goal", params: { files: [{ name: "Probe.g17", source: imageSource }], line: 0 } })).code, "invalid_params");
  assert.equal(failed(handleMachineRequest({ id: 29, method: "check", params: { files: [{ name: "Missing.g17" }] } })).code, "unknown_file");
  assert.equal(failed(handleMachineRequest(["not", "an", "object"])).code, "invalid_request");
  const response = handleMachineRequest({ id: 30, method: "check", params: { files: [{ name: "Probe.g17", source: imageSource }], foundation: "ZZ" } });
  assert.equal(JSON.stringify(response).includes("    at "), false);
  assert.throws(() => callMachineMethod("suggest", { files: [{ name: "Probe.g17", source: imageSource }], line: 10, tactic: "simp" }), /exact\?, apply\?, or rw\?/);
});

test("g17 serve answers newline-delimited requests and g17 check --json carries the protocol fields", () => {
  const requests = [
    JSON.stringify({ id: 1, method: "capabilities" }),
    "not json",
    JSON.stringify({ id: "two", method: "goal", params: { files: [{ name: "Broken.g17", source: brokenSource }], line: 11, column: 12 } }),
    JSON.stringify({ id: 3, method: "missing" }),
  ].join("\n") + "\n";
  const serve = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "serve"], { cwd: project, encoding: "utf8", input: requests });
  assert.equal(serve.status, 0, serve.stderr);
  const responses = serve.stdout.trim().split("\n").map(line => JSON.parse(line));
  assert.equal(responses.length, 4);
  assert.deepEqual(responses.map(item => item.id), [1, null, "two", 3]);
  assert.ok(responses.every(item => item.version === MACHINE_PROTOCOL_VERSION));
  assert.equal(responses[0].result.protocol, MACHINE_PROTOCOL_VERSION);
  assert.equal(responses[1].error.code, "invalid_request");
  assert.equal(responses[2].result.state.goals[0].goal, "x ∈ C");
  assert.equal(responses[3].error.code, "unknown_method");

  const check = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "check", "--json", "examples/Sets.g17"], { cwd: project, encoding: "utf8" });
  assert.equal(check.status, 0, check.stderr);
  const result = JSON.parse(check.stdout);
  assert.equal(result.version, MACHINE_PROTOCOL_VERSION);
  assert.equal(result.status, "checked");
  assert.equal(result.foundation.profile, "ZFG");
  assert.ok(result.theorems.length >= 7 && result.theorems.every((item: { status: string }) => item.status === "proved"));
  assert.deepEqual(result.diagnostics, []);
  const inProcess = ok<MachineCheckResult>(handleMachineRequest({ id: 31, method: "check", params: { files: [example("Sets.g17")] } }));
  assert.deepEqual(result.theorems.map((item: { steps: unknown }) => item.steps), inProcess.theorems.map(item => item.steps));

  const search = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "search", "--json", "name:transitive", "module:Set.Core"], { cwd: project, encoding: "utf8" });
  assert.equal(search.status, 0, search.stderr);
  assert.equal(JSON.parse(search.stdout).result.results[0].name, "Subset.transitive");
});

test("the Workbench's browser modules re-export the shared logic", async () => {
  const browserSearch = await import("../workbench/library-search.js");
  const generatedSearch = await import("../workbench/generated/src/library-search.js");
  assert.equal(browserSearch.LibrarySearchIndex, generatedSearch.LibrarySearchIndex);
  assert.equal(typeof browserSearch.scanSearchDeclarations, "function");
  const editor = await import("../workbench/editor-utils.js");
  const generatedNavigation = await import("../workbench/generated/src/workbench-navigation.js");
  assert.equal(editor.tacticStepAtCursor, generatedNavigation.tacticStepAtCursor);
  assert.equal(editor.resolveSymbolCandidate, generatedNavigation.resolveSymbolCandidate);
  assert.equal(editor.diagnosticSpan, generatedNavigation.diagnosticSpan);
  assert.equal(generatedNavigation.tacticStepAtCursor([{ line: 9, columnStart: 3 }], 9, 3), tacticStepAtCursor([{ line: 9, columnStart: 3 }], 9, 3));
});

const indirectSource = `module Indirect
import Grace.Cumulus.Set.Core

theorem both (x A B : Set)
  requires h : x ∈ A ∩ B
  shows x ∈ A
proof
  have split := intersection.membership at x, A, B
  rw split at h
  exact h.left
`;

const shadowSource = `module Shadow
import Grace.Cumulus.Set.Core

def evens (A : Set) : Set := { x ∈ A | x = x }

theorem evens.membership (x A : Set)
  shows x ∈ evens(A) ↔ (x ∈ A ∧ x = x)
proof
  simp [evens]
`;

test("check --imports notes every declaration used only through a transitive import", () => {
  const files = [{ name: "Indirect.g17", source: indirectSource }];
  const plain = ok<MachineCheckResult>(handleMachineRequest({ id: 40, method: "check", params: { files, moduleRoots: ["lib"] } }));
  assert.equal(plain.status, "checked");
  assert.deepEqual(plain.diagnostics, []);
  const audited = ok<MachineCheckResult>(handleMachineRequest({ id: 41, method: "check", params: { files, moduleRoots: ["lib"], imports: true } }));
  assert.equal(audited.status, "checked");
  const notes = audited.diagnostics.filter(item => item.severity === "note");
  assert.ok(notes.length >= 1, JSON.stringify(audited.diagnostics));
  assert.ok(notes.every(item => item.kind === "transitive-import" && item.file === "Indirect.g17" && item.theorem === "Indirect.both"));
  const membership = notes.find(item => item.declaration === "Grace.Cumulus.Set.Basic.Set.intersection.membership")!;
  assert.ok(membership, JSON.stringify(notes));
  assert.equal(membership.module, "Grace.Cumulus.Set.Basic");
  assert.equal(membership.via, "Grace.Cumulus.Set.Core");
  assert.equal(membership.path![0], "Grace.Cumulus.Set.Core");
  assert.equal(membership.path!.at(-1), "Grace.Cumulus.Set.Basic");
  assert.equal(membership.line, 4);
  assert.equal(membership.message,
    "Grace.Cumulus.Set.Basic.Set.intersection.membership is declared in Grace.Cumulus.Set.Basic, which Indirect reaches only through its import Grace.Cumulus.Set.Core; import Grace.Cumulus.Set.Basic directly");
  // A declaration of a direct import, of the module itself, or of the core is never noted.
  assert.ok(notes.every(item => !["Grace.Cumulus.Set.Core", "Indirect"].includes(item.module!) && !/^Grace\.Core(\.|$)/.test(item.module!)));
  // Each declaration once.
  assert.equal(new Set(notes.map(item => item.declaration)).size, notes.length);
});

test("check warns once per module about a theorem restating a generated property, and declaration answers with both", () => {
  const files = [{ name: "Shadow.g17", source: shadowSource }];
  const result = ok<MachineCheckResult>(handleMachineRequest({ id: 42, method: "check", params: { files, moduleRoots: ["lib"] } }));
  assert.equal(result.status, "checked");
  assert.equal(result.theorems[0]!.status, "proved");
  const warnings = result.diagnostics.filter(item => item.kind === "shadowed-property");
  assert.equal(warnings.length, 1, JSON.stringify(result.diagnostics));
  const warning = warnings[0]!;
  assert.equal(warning.severity, "warning");
  assert.equal(warning.line, 6);
  assert.equal(warning.theorem, "Shadow.evens.membership");
  assert.equal(warning.definition, "Shadow.evens");
  assert.deepEqual(warning.theorems, ["Shadow.evens.membership"]);
  assert.equal(warning.message,
    "Shadow restates a generated property as a theorem of the same name: evens.membership; such a name resolves to the theorem and hides the property");
  const declared = ok(handleMachineRequest({ id: 43, method: "declaration", params: { name: "evens.membership", files, moduleRoots: ["lib"] } }));
  assert.equal(declared.kind, "theorem");
  assert.equal(declared.name, "Shadow.evens.membership");
  assert.equal(declared.shadows.length, 1);
  assert.equal(declared.shadows[0].generated, true);
  assert.equal(declared.shadows[0].kind, "property");
  assert.equal(declared.shadows[0].definition, "Shadow.evens");
  assert.equal(declared.shadows[0].property, "membership");
  const plain = ok(handleMachineRequest({ id: 44, method: "declaration", params: { name: "Subset.transitive", module: "Grace.Cumulus.Set.Core" } }));
  assert.equal("shadows" in plain, false);
});

test("closure lists the import closure in dependency order with choice-freedom and the chain to a dependency", () => {
  const tube = ok(handleMachineRequest({ id: 45, method: "closure", params: { module: "Grace.Cumulus.Topology.Tube", from: "Set.Choice" } }));
  assert.equal(tube.module, "Grace.Cumulus.Topology.Tube");
  assert.equal(tube.file, "lib/Grace/Cumulus/Topology/Tube.g17");
  assert.equal(tube.choiceFree, false);
  assert.ok(tube.choice.includes("Grace.Cumulus.Set.Choice"));
  assert.equal(tube.count, tube.modules.length);
  assert.equal(tube.modules.at(-1).module, "Grace.Cumulus.Topology.Tube");
  // Dependencies come before dependents.
  const position = new Map(tube.modules.map((item: { module: string }, index: number) => [item.module, index]));
  for (const item of tube.modules) for (const imported of item.imports) assert.ok(position.get(imported)! < position.get(item.module)!, `${imported} before ${item.module}`);
  const choice = tube.modules.find((item: { module: string }) => item.module === "Grace.Cumulus.Set.Choice");
  assert.equal(choice.choiceFree, false);
  const basic = tube.modules.find((item: { module: string }) => item.module === "Grace.Cumulus.Set.Basic");
  assert.equal(basic.choiceFree, true);
  assert.equal(tube.from, "Grace.Cumulus.Set.Choice");
  assert.equal(tube.chain[0], "Grace.Cumulus.Topology.Tube");
  assert.equal(tube.chain.at(-1), "Grace.Cumulus.Set.Choice");
  for (let index = 1; index < tube.chain.length; index += 1) {
    assert.ok(tube.modules.find((item: { module: string }) => item.module === tube.chain[index - 1]).imports.includes(tube.chain[index]));
  }
  const natCore = ok(handleMachineRequest({ id: 46, method: "closure", params: { module: "Nat.Core" } }));
  assert.equal(natCore.module, "Grace.Cumulus.Nat.Core");
  assert.equal(natCore.choiceFree, true);
  assert.deepEqual(natCore.choice, []);
  assert.ok(natCore.modules.every((item: { choiceFree: boolean }) => item.choiceFree));
  const byFile = ok(handleMachineRequest({ id: 47, method: "closure", params: { file: "lib/Grace/Cumulus/Nat/Core.g17" } }));
  assert.deepEqual(byFile.modules.map((item: { module: string }) => item.module), natCore.modules.map((item: { module: string }) => item.module));
  assert.equal(failed(handleMachineRequest({ id: 48, method: "closure", params: { module: "Nat.Core", from: "Set.Choice" } })).code, "unknown_module");
  assert.equal(failed(handleMachineRequest({ id: 49, method: "closure", params: { module: "No.Such.Module" } })).code, "unknown_module");
  assert.equal(failed(handleMachineRequest({ id: 50, method: "closure", params: {} })).code, "invalid_params");
});

test("g17 check --imports, check --continue --quiet, and g17 closure print their text forms", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-imports-"));
  try {
    const indirect = join(directory, "Indirect.g17");
    const failing = join(directory, "Failing.g17");
    writeFileSync(indirect, indirectSource);
    writeFileSync(failing, "module Failing\nimport Grace.Cumulus.Set.Core\n\ntheorem wrong (A : Set)\n  shows A = ∅\nproof\n  settle\n");
    const g17 = (...args: string[]) => spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", ...args], { cwd: project, encoding: "utf8" });
    const audited = g17("check", "--imports", "--module-root", "lib", indirect);
    assert.equal(audited.status, 0, audited.stderr);
    assert.match(audited.stdout, /^note: .*Indirect\.g17:4: Grace\.Cumulus\.Set\.Basic\.Set\.intersection\.membership is declared in Grace\.Cumulus\.Set\.Basic/m);
    assert.match(audited.stdout, /^\d+ transitive-import notes?$/m);
    const json = g17("check", "--json", "--imports", "--module-root", "lib", indirect);
    assert.equal(json.status, 0, json.stderr);
    assert.ok(JSON.parse(json.stdout).diagnostics.some((item: { severity: string }) => item.severity === "note"));
    const quiet = g17("check", "--continue", "--quiet", "--module-root", "lib", indirect, failing);
    assert.equal(quiet.status, 1);
    assert.equal(quiet.stderr.trim(), "");
    const lines = quiet.stdout.trim().split("\n");
    assert.equal(lines.filter(line => line.startsWith("failed ")).length, 1, quiet.stdout);
    assert.equal(lines.filter(line => line.startsWith("checked ")).length, 0, quiet.stdout);
    assert.match(lines.at(-1)!, /^\d+ modules checked, 1 failed, 0 skipped$/);
    const loud = g17("check", "--continue", "--module-root", "lib", failing);
    assert.ok(loud.stdout.split("\n").some(line => line.startsWith("checked ")));
    const closure = g17("closure", "--text", "Topology.Tube", "--from", "Set.Choice");
    assert.equal(closure.status, 0, closure.stderr);
    assert.match(closure.stdout, /^Grace\.Cumulus\.Topology\.Tube: \d+ modules, uses Grace\.Cumulus\.Set\.Choice$/m);
    assert.match(closure.stdout, /^choice-free  Grace\.Cumulus\.Set\.Basic  lib\/Grace\/Cumulus\/Set\/Basic\.g17$/m);
    assert.match(closure.stdout, /^chain: Grace\.Cumulus\.Topology\.Tube → .*Grace\.Cumulus\.Set\.Choice$/m);
    const asJson = g17("closure", "Nat.Core");
    assert.equal(JSON.parse(asJson.stdout).result.choiceFree, true);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
