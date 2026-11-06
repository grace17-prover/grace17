// The Abhyankar–Sathaye blueprint is fully promoted into Cumulus: no module
// remains under blueprints/, every row of the README's module table names
// the library modules it became, the status block reports nothing left to
// prove, and the showcase theorems live in the library without admissions.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

const root = "blueprints/AbhyankarSathaye";
const library = "lib/Grace/Cumulus";

function g17Files(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? g17Files(path) : entry.name.endsWith(".g17") ? [path] : [];
  });
}

test("the Abhyankar–Sathaye blueprint is fully promoted into Cumulus", () => {
  assert.deepEqual(g17Files(root), [], "no blueprint module remains to be promoted");
  const readme = readFileSync(join(root, "README.md"), "utf8");
  const rows = readme.match(/^\| [A-Z][\w.]* \| \d \| [^|]+ \|$/gmu) ?? [];
  assert.ok(rows.length >= 17, `the module table has ${rows.length} rows`);
  for (const row of rows) {
    const home = row.split("|")[3]!.trim();
    assert.match(home, /^promoted: /u, row);
    for (const module of home.slice("promoted: ".length).split(",").map(item => item.trim())) {
      assert.ok(existsSync(join(library, `${module}.g17`)), `${module} is a Cumulus module`);
    }
  }
  const status = readme.slice(readme.indexOf("<!-- blueprint-status -->"), readme.indexOf("<!-- /blueprint-status -->"));
  assert.match(status, /\| \*\*total\*\* \| \*\*0\*\* \| \*\*0\*\* \| \*\*0\*\* \|/u);
  const theorem = readFileSync(join(library, "AlgebraicGeometry/Coordinates/Theorem.g17"), "utf8");
  assert.match(theorem, /^theorem counterexample$/mu);
  assert.match(theorem, /^theorem exists_noncoordinate_polynomial /mu);
  assert.doesNotMatch(theorem, /\bsorry\b/u);
});
