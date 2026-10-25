// The cycle double cover blueprint is complete: every module is promoted
// into Cumulus, the README records the library module each row became, and
// no admitted statement remains under the blueprint root.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

const root = "blueprints/CycleDoubleCover";
const library = "lib/Grace/Cumulus";

function g17Files(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? g17Files(path) : entry.name.endsWith(".g17") ? [path] : [];
  });
}

test("the cycle double cover blueprint is fully promoted into Cumulus", () => {
  assert.deepEqual(g17Files(root), [], "no blueprint module remains to be promoted");
  const readme = readFileSync(join(root, "README.md"), "utf8");
  // Every row of the module table names its promoted homes, and each home
  // is a library module.
  const rows = readme.match(/^\| [A-Z][\w.]* \| \d \| [^|]+ \|$/gmu) ?? [];
  assert.ok(rows.length >= 17, `the module table has ${rows.length} rows`);
  for (const row of rows) {
    const home = row.split("|")[3]!.trim();
    assert.match(home, /^promoted: /u, row);
    for (const module of home.slice("promoted: ".length).split(",").map(item => item.trim())) {
      assert.ok(existsSync(join(library, `${module}.g17`)), `${module} is a Cumulus module`);
    }
  }
  // The status block reports nothing left to prove.
  const status = readme.slice(readme.indexOf("<!-- blueprint-status -->"), readme.indexOf("<!-- /blueprint-status -->"));
  assert.match(status, /\| \*\*total\*\* \| \*\*0\*\* \| \*\*0\*\* \| \*\*0\*\* \|/u);
  // The showcase theorem lives in the library without admissions.
  const theorem = readFileSync(join(library, "GraphTheory/DoubleCover/Theorem.g17"), "utf8");
  assert.match(theorem, /^theorem cycleDoubleCover /mu);
  assert.doesNotMatch(theorem, /\bsorry\b/u);
});
