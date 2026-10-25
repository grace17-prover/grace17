// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The machine interface under a proving campaign: a long-running process
// re-reading a dependency rewritten on disk, name lookups in a workspace
// whose active file does not check, the dependent status of a complete
// proof that cites an admission, the caption of a trace that starts inside
// a block, and a serve session over a run of workspace requests.

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { handleMachineRequest, MACHINE_PROTOCOL_VERSION, theoremStatus, type MachineCheckResult } from "../src/machine-interface.ts";

const project = fileURLToPath(new URL("..", import.meta.url));

function ok<T = Record<string, any>>(response: ReturnType<typeof handleMachineRequest>): T {
  assert.equal(response.ok, true, JSON.stringify(response));
  assert.equal(response.version, MACHINE_PROTOCOL_VERSION);
  return (response as { result: T }).result;
}

function failed(response: ReturnType<typeof handleMachineRequest>): { code: string; message: string; [detail: string]: unknown } {
  assert.equal(response.ok, false, JSON.stringify(response));
  return (response as { error: { code: string; message: string } }).error;
}

// A dependency module in two states: a proof that checks, and one whose
// last step establishes the wrong fact.
const lemmas = (ending: string) => `module Camp.Lemmas
import Grace.Cumulus.Set.Core

theorem subset_chain (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  unfold Subset
  intro x
  intro hx
  ${ending}
`;
const goodLemmas = lemmas("exact second with x, (first with x, hx)");
const brokenLemmas = lemmas("exact first with x, hx");

const useSource = `module Camp.Use
import Lemmas

theorem chain_twice (A B C D : Set)
  requires ab : A ⊆ B
  requires bc : B ⊆ C
  requires cd : C ⊆ D
  shows A ⊆ D
proof
  have ac := subset_chain with ab, bc
  exact subset_chain with ac, cd
`;

function campaignRoot(dependency: string): { root: string; lemmasFile: string; useFile: string } {
  const root = mkdtempSync(join(tmpdir(), "g17-campaign-"));
  mkdirSync(join(root, "Camp"));
  const lemmasFile = join(root, "Camp", "Lemmas.g17");
  const useFile = join(root, "Camp", "Use.g17");
  writeFileSync(lemmasFile, dependency);
  writeFileSync(useFile, useSource);
  return { root, lemmasFile, useFile };
}

test("check re-reads a dependency rewritten on disk within one process", () => {
  const { root, lemmasFile, useFile } = campaignRoot(brokenLemmas);
  try {
    const params = { files: [{ name: useFile }], activeFile: useFile, moduleRoots: [root] };
    const before = ok<MachineCheckResult>(handleMachineRequest({ id: 1, method: "check", params }));
    assert.equal(before.status, "failed");
    assert.equal(before.diagnostics[0]!.file, lemmasFile);
    // The dependency is repaired on disk; the same workspace, asked again
    // in the same process, is checked over the repaired file.
    writeFileSync(lemmasFile, goodLemmas);
    const after = ok<MachineCheckResult>(handleMachineRequest({ id: 2, method: "check", params }));
    assert.equal(after.status, "checked", JSON.stringify(after.diagnostics));
    assert.deepEqual(after.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status]), [["Camp.Use.chain_twice", "proved"]]);
    const found = ok(handleMachineRequest({ id: 3, method: "declaration", params: { ...params, name: "subset_chain" } }));
    assert.equal(found.name, "Camp.Lemmas.subset_chain");
    assert.equal(found.partial, undefined);
    // And a dependency broken again is seen again: no stale success either.
    writeFileSync(lemmasFile, brokenLemmas);
    const again = ok<MachineCheckResult>(handleMachineRequest({ id: 4, method: "check", params }));
    assert.equal(again.status, "failed");
    assert.equal(again.diagnostics[0]!.file, lemmasFile);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

// A file whose last theorem's proof is broken, after one that checks.
const midProofSource = `module Probe
import Grace.Cumulus.Set.Core

theorem early (A B : Set)
  requires h : A ⊆ B
  shows A ⊆ B
proof
  exact h

theorem late (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  exact first

theorem afterwards (A : Set)
  shows A ⊆ A
proof
  exact Subset.reflexive at A
`;

test("declaration and signature answer from what loaded when the active file fails", () => {
  const files = [{ name: "Probe.g17", source: midProofSource }];
  const checked = ok<MachineCheckResult>(handleMachineRequest({ id: 1, method: "check", params: { files } }));
  assert.equal(checked.status, "failed");
  const failureLine = checked.diagnostics[0]!.line;
  // A library name resolves in the dependencies that loaded.
  const library = ok(handleMachineRequest({ id: 2, method: "declaration", params: { files, name: "Subset.transitive" } }));
  assert.equal(library.name, "Grace.Cumulus.Set.Core.Subset.transitive");
  assert.equal(library.elaborated, true);
  assert.equal(library.partial, true);
  assert.equal(library.checkFailed.file, "Probe.g17");
  assert.equal(library.checkFailed.line, failureLine);
  assert.match(library.checkFailed.message, /establishes/);
  // An earlier theorem of the file resolves too, with its statement.
  const earlier = ok(handleMachineRequest({ id: 3, method: "declaration", params: { files, name: "early" } }));
  assert.equal(earlier.name, "Probe.early");
  assert.equal(earlier.kind, "theorem");
  assert.equal(earlier.partial, true);
  assert.match(earlier.statement, /A ⊆ B → A ⊆ B/);
  // A theorem after the failure is known from the source and said to be
  // out of the environment for that reason.
  const later = ok(handleMachineRequest({ id: 4, method: "declaration", params: { files, name: "afterwards" } }));
  assert.equal(later.inScope, false);
  assert.equal(later.partial, true);
  assert.match(later.message, /after the failure at line \d+/);
  // signature elaborates from the same environment, and search is unaffected.
  const signature = ok(handleMachineRequest({ id: 5, method: "signature", params: { files, name: "Subset.transitive", elaborate: true } }));
  assert.equal(signature.elaborated, true);
  assert.equal(signature.partial, true);
  assert.equal(signature.checkFailed.line, failureLine);
  assert.deepEqual(signature.positional.at, ["A", "B", "C"]);
  const search = ok(handleMachineRequest({ id: 6, method: "search", params: { files, query: "name:transitive module:Set.Core" } }));
  assert.ok(search.results.some((item: { name: string }) => item.name.endsWith("Subset.transitive")));
  // A workspace whose import cannot be resolved loaded nothing: a library
  // name is then out of scope, and the answer still says why.
  const unresolved = ok(handleMachineRequest({ id: 7, method: "declaration", params: { files: [{ name: "Lost.g17", source: "module Lost\nimport No.Such.Module\n" }], name: "Subset.transitive" } }));
  assert.equal(unresolved.inScope, false);
  assert.equal(unresolved.partial, true);
  assert.match(unresolved.checkFailed.message, /cannot locate imported module No\.Such\.Module/);
  assert.equal(failed(handleMachineRequest({ id: 8, method: "notations", params: { files: [{ name: "Lost.g17", source: "module Lost\nimport No.Such.Module\n" }] } })).code, "check_failed");
});

const admittedSource = `module Admitted
import Grace.Cumulus.Set.Core

theorem unfinished (x : Set)
  shows x = x
proof
  sorry
`;

const userSource = `module User
import Admitted

theorem downstream (x : Set)
  shows x = x
proof
  exact unfinished at x

theorem own (x : Set)
  shows x = x
proof
  rfl
`;

test("a complete proof citing an admitted theorem is dependent, and its file has no obligation of its own", () => {
  assert.equal(theoremStatus({ name: "T", sorries: [] }), "proved");
  assert.equal(theoremStatus({ name: "T", sorries: [{ theorem: "T" }] }), "admitted");
  assert.equal(theoremStatus({ name: "T", sorries: [{ theorem: "S" }] }), "dependent");
  assert.equal(theoremStatus({ name: "T", sorries: [{ theorem: "S" }, { theorem: "T" }] }), "admitted");
  const files = [{ name: "Admitted.g17", source: admittedSource }, { name: "User.g17", source: userSource }];
  // The importing file alone: its theorems are dependent or proved, its own
  // sorry count is zero, and the admission it rests on is still named.
  const user = ok<MachineCheckResult>(handleMachineRequest({ id: 1, method: "check", params: { files, activeFile: "User.g17" } }));
  assert.equal(user.status, "checked");
  const statuses = Object.fromEntries(user.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status]));
  assert.deepEqual(statuses, { "User.downstream": "dependent", "User.own": "proved" });
  const downstream = user.theorems.find(theorem => (theorem as { name?: string }).name === "User.downstream")!;
  assert.equal(downstream.sorries.length, 1);
  assert.equal(downstream.sorries[0]!.theorem, "Admitted.unfinished");
  assert.equal(downstream.sorries[0]!.file, "Admitted.g17");
  const summary = user.files.find(file => file.name === "User.g17") as Record<string, unknown>;
  assert.equal(summary.sorries, 0);
  assert.equal(summary.admittedSorries, 1);
  assert.equal(summary.dependentTheorems, 1);
  assert.equal(summary.admittedTheorems, 0);
  // Both files reported: the admission's own theorem is admitted.
  const both = ok<MachineCheckResult>(handleMachineRequest({ id: 2, method: "check", params: { files } }));
  const all = Object.fromEntries(both.theorems.map(theorem => [(theorem as { name?: string }).name, theorem.status]));
  assert.deepEqual(all, { "Admitted.unfinished": "admitted", "User.downstream": "dependent", "User.own": "proved" });
  const admitted = both.files.find(file => file.name === "Admitted.g17") as Record<string, unknown>;
  assert.equal(admitted.sorries, 1);
  assert.equal(admitted.admittedTheorems, 1);
  assert.equal(admitted.dependentTheorems, 0);
  // The same within one file: a later theorem citing an earlier sorry.
  const single = ok<MachineCheckResult>(handleMachineRequest({ id: 3, method: "check", params: { files: [{ name: "One.g17", source: `${admittedSource}
theorem downstream (x : Set)
  shows x = x
proof
  exact unfinished at x
` }] } }));
  assert.deepEqual(single.theorems.map(theorem => theorem.status), ["admitted", "dependent"]);
  // The CLI's --json check carries the same statuses over its own loader.
  const root = mkdtempSync(join(tmpdir(), "g17-dependent-"));
  try {
    writeFileSync(join(root, "Admitted.g17"), admittedSource);
    writeFileSync(join(root, "User.g17"), userSource);
    const run = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "check", "--module-root", "lib", "--module-root", root, join(root, "User.g17")], { cwd: project, encoding: "utf8" });
    assert.equal(run.status, 0, run.stderr);
    // The admitted module was checked in the same run, so its own sorry is
    // the warning; the dependent proof is the note.
    assert.match(run.stdout, /warning: 1 proof obligation was admitted with sorry/);
    assert.match(run.stdout, /note: 1 complete proof depends on 1 admission elsewhere: sorry\.Admitted\.unfinished\./);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("goal captions a trace that starts inside a by block as the block's start", () => {
  const source = `module Nested
import Grace.Cumulus.Set.Core

theorem viaBy (A B C : Set)
  requires hAB : A ⊆ B
  requires hBC : B ⊆ C
  shows A ⊆ C
proof
  have same : A ⊆ A := Subset.reflexive at A
  have mid : A ⊆ B by exact hBC
  exact Subset.transitive with mid, hBC
`;
  const files = [{ name: "Nested.g17", source }];
  // The failure is in the by block on line 10; its trace is that block's.
  const before = ok(handleMachineRequest({ id: 1, method: "goal", params: { files, line: 9, column: 1 } }));
  assert.equal(before.theoremStatus, "failed");
  assert.equal(before.step, 0);
  assert.equal(before.state.goals[0].goal, "A ⊆ B");
  assert.equal(before.caption, "Current goal, at the start of the block on line 10");
  const start = ok(handleMachineRequest({ id: 2, method: "goal", params: { files, line: 8, column: 1 } }));
  assert.equal(start.caption, "Current goal, at the start of the block on line 10");
  // A trace that begins with the proof keeps the theorem-start caption.
  const whole = source.replace("have mid : A ⊆ B by exact hBC", "have mid : A ⊆ B\n    exact hBC");
  const plain = ok(handleMachineRequest({ id: 3, method: "goal", params: { files: [{ name: "Nested.g17", source: whole }], line: 9, column: 1 } }));
  assert.equal(plain.theoremStatus, "failed");
  assert.equal(plain.step, 0);
  assert.equal(plain.state.goals[0].goal, "A ⊆ C");
  assert.equal(plain.caption, "Current goal, at theorem start");
});

test("serve answers a run of workspace declaration requests and request errors without exiting", () => {
  const { root, useFile } = campaignRoot(goodLemmas);
  try {
    const workspace = { files: [{ name: useFile }], activeFile: useFile, moduleRoots: [root] };
    const names = ["subset_chain", "Subset.transitive", "chain_twice", "union2.subset", "subset_chain"];
    const requests = [
      ...names.map((name, index) => JSON.stringify({ id: index + 1, method: "declaration", params: { ...workspace, name } })),
      "{not json",
      JSON.stringify({ id: "bad", method: "declaration", params: { ...workspace, name: 7 } }),
      JSON.stringify({ id: "none", method: "nothing" }),
      JSON.stringify({ id: "last", method: "declaration", params: { ...workspace, name: "chain_twice" } }),
    ].join("\n") + "\n";
    const serve = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "serve"], { cwd: project, encoding: "utf8", input: requests });
    assert.equal(serve.status, 0, serve.stderr);
    const responses = serve.stdout.trim().split("\n").map(line => JSON.parse(line));
    assert.equal(responses.length, names.length + 4);
    assert.deepEqual(responses.map(item => item.id), [1, 2, 3, 4, 5, null, "bad", "none", "last"]);
    assert.deepEqual(responses.slice(0, names.length).map(item => item.result?.name), [
      "Camp.Lemmas.subset_chain", "Grace.Cumulus.Set.Core.Subset.transitive", "Camp.Use.chain_twice", "Grace.Cumulus.Set.Core.union2.subset", "Camp.Lemmas.subset_chain",
    ]);
    assert.equal(responses[5].error.code, "invalid_request");
    assert.equal(responses[6].error.code, "invalid_params");
    assert.equal(responses[7].error.code, "unknown_method");
    assert.equal(responses[8].result.name, "Camp.Use.chain_twice");
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
