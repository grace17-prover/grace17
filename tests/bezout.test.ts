// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module BezoutRegression\nimport Grace.Cumulus.NumberTheory\n";

test("Bézout existence and a signed certificate check through the public import", () => {
  const source = readFileSync("examples/BezoutStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "BezoutStarter.g17", source }]).ok, true);
});

test("Bézout descent retains intermediate goals cold and after an edit", () => {
  const file = { name: "NumberTheory/Bezout.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/Bezout.g17", "utf8") };
  const start = performance.now();
  prepareWorkbenchFiles([file], "ZFG", file.name);
  const prepared = performance.now();
  const first = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  const checked = performance.now();
  assert.equal(first.ok, true);
  const descent = first.theorems.find(t => t.name.endsWith("gcdSteps.bezout"));
  assert.ok(descent?.steps.some(s => s.after.goals.length > 0));
  assert.equal(descent?.steps.at(-1)?.after.goals.length, 0);
  file.source += "\n-- edited Bézout descent\n";
  const edited = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  assert.equal(edited.ok, true);
  assert.ok(edited.theorems.find(t => t.name.endsWith("gcdSteps.bezout"))?.steps.some(s => s.after.goals.length > 0));
  console.log(`Bézout timings: prepare ${(prepared-start).toFixed(1)} ms; cold ${(checked-prepared).toFixed(1)} ms; edited ${(performance.now()-checked).toFixed(1)} ms`);
});

test("a wrong signed Bézout coefficient is rejected", () => {
  const source = readFileSync("examples/BezoutStarter.g17", "utf8").replace("integerNegativeOfNat(2), 54", "integerNegativeOfNat(3), 54");
  assert.throws(() => checkWorkbenchFiles([{ name: "BezoutStarter.g17", source }]));
});

test("Euclidean coefficient transport requires its division equation", () => {
  const source = header + `theorem missing_equation (u v : Integer, a b q r : Nat)
  shows integerLinearCombination(v, u + (-(integerOfNat(q) * v)), a, b) = integerLinearCombination(u, v, b, r)
proof
  exact integerLinearCombination.euclidean_step at u, v, a, b, q, r with *
`;
  assert.throws(() => checkWorkbenchFiles([{ name: "BezoutRegression.g17", source }]));
});

test("quotient multiplication identifies different representatives of the same negative result", () => {
  const source = header + `theorem negative_product
  shows integerMulValue(integerClass(1, 3), integerClass(8, 5)) = integerClass(4, 10)
proof
  simp [integerMulValue.classes, integerClassMul]
  apply integerClass.eq at 1 * 8 + 3 * 5, 1 * 5 + 3 * 8, 4, 10 with *{4}
  compute
`;
  assert.equal(checkWorkbenchFiles([{ name: "BezoutRegression.g17", source }]).ok, true);
  assert.throws(() => checkWorkbenchFiles([{ name: "BezoutRegression.g17", source: source.replaceAll("4, 10", "10, 4") }]));
});

test("nested existential simpa succeeds in a small heap and rejects an incorrect target", async () => {
  const { spawnSync } = await import("node:child_process");
  const source = header + `theorem transported (a b : Nat)
  shows ∃ u, Integer(u) ∧ ∃ v, Integer(v) ∧
    integerLinearCombination(u, v, a, b) = integerOfNat(gcd(a, b))
proof
  have bound := LessEqual.reflexive at b with *
  have coefficients := gcdSteps.bezout at b, a, b with *, bound
  simpa [gcd] using coefficients
`;
  const runner = `import {checkWorkbenchFiles} from './src/workbench.ts';
const source=${JSON.stringify(source)};
if (!checkWorkbenchFiles([{name:'BezoutRegression.g17',source}]).ok) process.exit(2);
const wrong=source.replace('integerOfNat(gcd(a, b))','integerOfNat(succ(gcd(a, b)))');
let rejected=false;
try {checkWorkbenchFiles([{name:'BezoutRegression.g17',source:wrong}]);} catch (e) {rejected=true; console.log(e.message);}
if(!rejected) process.exit(3);`;
  const result = spawnSync(process.execPath, ["--max-old-space-size=768", "--disable-warning=ExperimentalWarning", "--input-type=module", "-e", runner], { encoding: "utf8", timeout: 90_000 });
  assert.equal(result.status, 0, result.stderr + result.stdout + String(result.error ?? ""));
  assert.match(result.stdout, /settle stopped|did not close|unable to/);
});
