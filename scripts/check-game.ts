// Check every Set Theory Game level: the starter checks modulo its sorry and
// the solution checks completely. Run as `node scripts/check-game.ts`.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { checkWorkbenchFiles } from "../src/workbench.ts";
import { levelSource, worlds } from "../workbench/game-levels.js";

let failures = 0;
const only = process.argv[2];
for (const world of worlds) {
  for (const level of world.levels) {
    if (only && !`${world.id}.${level.id}`.includes(only)) continue;
    const label = `${world.id}/${level.id}`;
    const started = Date.now();
    for (const [mode, proof] of [["starter", level.starter], ["solution", level.solution]] as const) {
      const source = levelSource(world, level, proof);
      const name = `${world.id}-${level.id}.g17`;
      try {
        const result = checkWorkbenchFiles([{ name, source }], "ZFG", [name], { includeKernelDetails: false });
        const sorries = result.theorems.flatMap((theorem: { sorries?: unknown[] }) => theorem.sorries ?? []).length;
        if (!result.ok) { failures++; console.log(`FAIL ${label} ${mode}: ${result.message}`); }
        else if (mode === "solution" && sorries > 0) { failures++; console.log(`FAIL ${label} solution still has ${sorries} sorry`); }
        else if (mode === "starter" && sorries === 0) { failures++; console.log(`FAIL ${label} starter has no sorry`); }
      } catch (error) {
        failures++;
        console.log(`FAIL ${label} ${mode}: ${error instanceof Error ? error.message.split("\n")[0] : String(error)}`);
      }
    }
    console.log(`${label} ${Date.now() - started}ms`);
  }
}
console.log(failures ? `${failures} failing level checks` : "all levels check");
process.exit(failures ? 1 : 0);
