#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Compare the same initialization theorem with explicit and automated scripts.
// Fresh kernels prevent declaration-cache hits; dependencies are outside timing.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { performance } from "node:perf_hooks";
import { compileProofModule, createZfgKernel, elaborateModule, exportTheoremForMachine,
  formulaEquals, loadModuleGraph, verifyProofMachine } from "../src/index.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));
const graph = `${library}/Grace/Cumulus/GraphTheory`;
const sources = {
  explicit: readFileSync(new URL("fixtures/DijkstraInvariant.explicit.g17", import.meta.url), "utf8"),
  automated: readFileSync(`${graph}/DijkstraInvariant.g17`, "utf8"),
};
const name = "Grace.Cumulus.GraphTheory.DijkstraInvariant.Dijkstra.StateInvariant.initial";
const measurements: Record<string, unknown>[] = [];
let statement: ReturnType<typeof exportTheoremForMachine>["statement"] | undefined;
for (let round = 0; round < 3; round += 1) {
  const order = round % 2 ? ["automated", "explicit"] as const : ["explicit", "automated"] as const;
  for (const variant of order) {
    const kernel = createZfgKernel();
    loadModuleGraph(kernel, [`${graph}/DijkstraProgress.g17`, `${graph}/DijkstraCut.g17`], [library]);
    if (variant === "automated" && round === 0) {
      const disabled = sources.automated.replace(/ \(backchain := 2, work := 512\)/g, "");
      const isolated = createZfgKernel();
      loadModuleGraph(isolated, [`${graph}/DijkstraProgress.g17`, `${graph}/DijkstraCut.g17`], [library]);
      assert.throws(() => elaborateModule(isolated, disabled), /local proof sourceZero is incomplete/);
    }
    const started = performance.now();
    elaborateModule(kernel, sources[variant]);
    const elaborationMs = performance.now() - started;
    const exported = exportTheoremForMachine(kernel, name);
    if (statement && !formulaEquals(statement, exported.statement)) throw new Error("initialization statements differ");
    statement = exported.statement;
    const tape = compileProofModule([exported]);
    const replayStarted = performance.now();
    const replay = verifyProofMachine(kernel, tape);
    const replayMs = performance.now() - replayStarted;
    const body = sources[variant].split("theorem StateInvariant.initial")[1]!.split("proof\n")[1]!.split("\nend Dijkstra")[0]!;
    measurements.push({ round: round + 1, variant, moduleElaborationMs: elaborationMs, theoremReplayMs: replayMs,
      theoremInstructions: replay.stats.instructions, proofCharacters: body.length, proofLines: body.split("\n").filter(line => line.trim()).length,
      explicitAt: (body.match(/\bat\b/g) ?? []).length, localHave: (body.match(/\bhave\b/g) ?? []).length });
  }
}
console.log(JSON.stringify({ scope: "Whole invariant module elaboration; initialization-only proof tape and replay. Fresh kernels, preloaded dependencies, three alternating rounds.", measurements }, null, 2));
