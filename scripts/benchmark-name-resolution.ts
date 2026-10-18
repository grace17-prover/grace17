// Isolated name-resolution hit/miss/ambiguity measurements; no proof search.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { NameResolutionIndex, AmbiguousNameError } from "../src/name-resolution.ts";
import { readFileSync } from "node:fs";
const results = [];
for (const unrelated of [1000, 10000, 100000]) {
  const index = new NameResolutionIndex();
  const symbols = new Set<string>();
  for (let i = 0; i < unrelated; i++) {
    const name = `Other.N${i}.item${i}`;
    symbols.add(name); index.register(name, `File${i}`);
  }
  const opens = Array.from({ length: 100 }, (_, i) => `Open${i}`);
  for (const name of ["Open3.hit", "Open4.collision", "Open5.collision"])
    { symbols.add(name); index.register(name, "Provider"); }
  const namespaces: readonly string[] = [];
  const exists = (name: string) => symbols.has(name);
  const cases: Record<string, () => void> = {
    hit: () => { index.resolve("hit", namespaces, opens, exists); },
    miss: () => { index.resolve("absent", namespaces, opens, exists); },
    ambiguity: () => { try { index.resolve("collision", namespaces, opens, exists); }
      catch (error) { if (!(error instanceof AmbiguousNameError)) throw error; } },
  };
  const timings: Record<string, number> = {};
  for (const [name, action] of Object.entries(cases)) {
    for (let i = 0; i < 2000; i++) action();
    const samples = [];
    for (let sample = 0; sample < 5; sample++) {
      const start = performance.now();
      for (let i = 0; i < 10000; i++) action();
      samples.push((performance.now() - start) * 1000 / 10000);
    }
    timings[name] = samples.sort((a, b) => a - b)[2]!;
  }
  const cold: Record<string, number> = {};
  for (const kind of ["hit", "miss", "ambiguity"]) {
    if (kind !== "miss") for (let i = 0; i < 1000; i++) {
      for (const prefix of kind === "hit" ? ["Open3"] : ["Open4", "Open5"]) {
        const name = `${prefix}.${kind}${i}`;
        symbols.add(name); index.register(name, "Provider");
      }
    }
    const samples = [];
    for (let batch = 0; batch < 5; batch++) {
      const start = performance.now();
      for (let i = batch * 200; i < (batch + 1) * 200; i++) {
        try { index.resolve(`${kind}${i}`, namespaces, opens, exists); }
        catch (error) { if (!(error instanceof AmbiguousNameError)) throw error; }
      }
      samples.push((performance.now() - start) * 1000 / 200);
    }
    cold[kind] = samples.sort((a, b) => a - b)[2]!;
  }
  results.push({ firstLookupMedianMicroseconds: cold, unrelatedDeclarations: unrelated, openedNamespaces: opens.length, medianMicrosecondsPerLookup: timings });
}
console.log(JSON.stringify({ version: JSON.parse(readFileSync("package.json", "utf8")).version,
  node: process.version, methodology: "Single isolated process; five batches of 10,000 warm queries per case; ambiguity includes Error construction and its candidate message; first lookups use five batches of 200 distinct names, with registration outside the timer; excludes registry construction and proof elaboration.", results }, null, 2));
