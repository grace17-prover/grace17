// The Arithmetic blueprint is fully promoted into Cumulus: no module remains
// under blueprints/, every row of the README's module table names the
// library module it became, the status block reports nothing left to prove,
// and the four headline theorems live in the library without admissions.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

const root = "blueprints/Arithmetic";
const library = "lib/Grace/Cumulus";

function g17Files(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? g17Files(path) : entry.name.endsWith(".g17") ? [path] : [];
  });
}

test("the Arithmetic blueprint is fully promoted into Cumulus", () => {
  assert.deepEqual(g17Files(root), [], "no blueprint module remains to be promoted");
  const readme = readFileSync(join(root, "README.md"), "utf8");
  const rows = readme.match(/^\| [A-Z][\w.]* \| \d \| [^|]+ \|$/gmu) ?? [];
  assert.ok(rows.length >= 19, `the module table has ${rows.length} rows`);
  for (const row of rows) {
    const home = row.split("|")[3]!.trim();
    assert.match(home, /^promoted: /u, row);
    for (const module of home.slice("promoted: ".length).split(",").map(item => item.trim())) {
      assert.ok(existsSync(join(library, `${module}.g17`)), `${module} is a Cumulus module`);
    }
  }
  const status = readme.slice(readme.indexOf("<!-- blueprint-status -->"), readme.indexOf("<!-- /blueprint-status -->"));
  assert.match(status, /\| \*\*total\*\* \| \*\*0\*\* \| \*\*0\*\* \| \*\*0\*\* \|/u);
  const headlines: [string, RegExp][] = [
    ["NumberTheory/QuadraticReciprocity.g17", /^theorem quadratic_reciprocity /mu],
    ["NumberTheory/TwoSquares.g17", /^theorem fermat\.two_squares /mu],
    ["NumberTheory/FourSquares.g17", /^theorem lagrange\.four_squares /mu],
    ["NumberTheory/Pell.g17", /^theorem pell\.exists_nontrivial /mu],
  ];
  for (const [file, pattern] of headlines) {
    const source = readFileSync(join(library, file), "utf8");
    assert.match(source, pattern, file);
    assert.doesNotMatch(source, /\bsorry\b/u, file);
  }
});
