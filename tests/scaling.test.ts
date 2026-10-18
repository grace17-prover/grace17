// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  KernelError, app, assume, checkProofDag, countProofDagTree, createZfgKernel, congr, definition, encodeProofDag,
  eq, formulaEquals, impElim, impIntro, loadModuleSourceGraph, or, pred, prepareRewrites, refl, settle, v,
  type Proof, type SettleStats, type Term,
} from "../src/index.ts";
import { buildArithmeticSuite } from "../examples/arithmetic-suite.ts";
import { fileURLToPath } from "node:url";

test("indexes a thousand irrelevant rewrite rules away from arithmetic terms", () => {
  const { kernel } = buildArithmeticSuite();
  const rules: Proof[] = [
    definition("plus", "equation.0"),
    definition("plus", "equation.1"),
  ];
  for (let index = 0; index < 1_000; index += 1) {
    const name = `noise${index}`;
    kernel.defineFunction(name, ["x"], v("x"));
    rules.push(definition(name));
  }
  const prepared = prepareRewrites(kernel, rules);
  const numeral = (value: number) => {
    let result = app("zero");
    for (let index = 0; index < value; index += 1) result = app("succ", result);
    return result;
  };
  const goal = eq(app("plus", numeral(4), numeral(5)), numeral(9));
  const stats: SettleStats = { rules: 0, termsVisited: 0, candidatesConsidered: 0, rewrites: 0 };
  const proof = settle(kernel, goal, { using: prepared, stats });
  assert.equal(formulaEquals(kernel.checkProof(proof), goal), true);
  assert.equal(stats.rules, 1_002);
  assert.ok(stats.candidatesConsidered < 50, `considered ${stats.candidatesConsidered} candidates`);
});

test("settle transports a representative inequality through coordinate equalities without branching", { timeout: 2_000 }, () => {
  const kernel = createZfgKernel();
  kernel.declareFunction("mul2", 2);
  kernel.declareFunction("add2", 2);
  kernel.declarePredicate("Less2", 2);
  const [a, b, m, c, d, n, wa, wb, wm, wc, wd, wn] =
    ["a", "b", "m", "c", "d", "n", "wa", "wb", "wm", "wc", "wd", "wn"].map(v) as
      [Term, Term, Term, Term, Term, Term, Term, Term, Term, Term, Term, Term];
  const sum = (x: Term, y: Term, z: Term, w: Term) => app("add2", app("mul2", x, y), app("mul2", z, w));
  const witnessed = pred("Less2", sum(wn, wa, wm, wd), sum(wm, wc, wn, wb));
  const goal = pred("Less2", sum(n, a, m, d), sum(m, c, n, b));
  const assumptions = [
    eq(a, wa), eq(b, wb), eq(m, wm), eq(c, wc), eq(d, wd), eq(n, wn), witnessed,
  ];
  const proof = settle(kernel, goal, { using: [], assumptions });
  assert.equal(formulaEquals(kernel.checkProof(proof, assumptions), goal), true);
});

test("settle stops pathological branching at its logical search budget", { timeout: 500 }, () => {
  const kernel = createZfgKernel();
  kernel.declarePredicate("Unreachable", 0);
  const assumptions = Array.from({ length: 24 }, (_, index) => {
    kernel.declarePredicate(`Left${index}`, 0);
    kernel.declarePredicate(`Right${index}`, 0);
    return or(pred(`Left${index}`), pred(`Right${index}`));
  });
  assert.throws(
    () => settle(kernel, pred("Unreachable"), { using: [], assumptions, fuel: 8 }),
    /settle stopped after 8 logical search steps; use a structural tactic or give settle a smaller relevant rule set/,
  );
});

test("ring and arith remain responsive with a thousand irrelevant hypotheses", { timeout: 15_000 }, () => {
  const library = fileURLToPath(new URL("../lib", import.meta.url));
  const noise = Array.from({ length: 1_000 }, (_, index) =>
    `  requires noise${index} : empty = singleton(empty)`).join("\n");
  const source = `module User.LargeAutomationContext
namespace User.LargeAutomationContext
import Grace.Cumulus.Nat

theorem ring.scale (a b c d : Nat)
${noise}
  shows (a + b) + (c + d) = (a + c) + (b + d)
proof
  ring

theorem arith.scale (a b c : Nat)
${noise}
  requires h : a + c = b + c
  shows a = b
proof
  arith

theorem arith.inequality_scale (x y : Nat)
${noise}
  requires hx : x > 2
  requires hy : y ≥ 3
  shows x + y > 5
proof
  arith

end User.LargeAutomationContext
`;
  const loaded = loadModuleSourceGraph(createZfgKernel(), [{ file: "LargeAutomationContext.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.LargeAutomationContext.ring.scale",
    "User.LargeAutomationContext.arith.scale",
    "User.LargeAutomationContext.arith.inequality_scale",
  ]);
});

test("arith remains responsive with hundreds of irrelevant Nat inequalities", { timeout: 15_000 }, () => {
  const library = fileURLToPath(new URL("../lib", import.meta.url));
  const count = 400;
  const definitions = Array.from({ length: count }, (_, index) =>
    `def noise${index} : Nat := 0`).join("\n");
  const noise = Array.from({ length: count }, (_, index) =>
    `  requires hnoise${index} : noise${index} ≤ noise${index} + 1`).join("\n");
  const source = `module User.LargeNatArithmeticContext
namespace User.LargeNatArithmeticContext
import Grace.Cumulus.Nat

${definitions}

theorem arith.relevant_component (x y : Nat)
${noise}
  requires hxy : x ≤ y
  shows x ≤ y + 1
proof
  arith

end User.LargeNatArithmeticContext
`;
  const loaded = loadModuleSourceGraph(createZfgKernel(), [{ file: "LargeNatArithmeticContext.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    ...Array.from({ length: count }, (_, index) => `User.LargeNatArithmeticContext.noise${index}.type`),
    "User.LargeNatArithmeticContext.arith.relevant_component",
  ]);
});

test("hash-conses and cached-checks a highly shared proof DAG", () => {
  const { kernel } = buildArithmeticSuite();
  let proof: Proof = refl(app("zero"));
  for (let depth = 0; depth < 10; depth += 1) proof = congr("pair", proof, proof);
  const dag = encodeProofDag(proof);
  const checked = checkProofDag(kernel, dag);
  assert.equal(checked.dagNodes, 11);
  assert.equal(checked.treeNodes, 2_047);
  assert.equal(checked.stats.nodesVisited, 11);
  assert.equal(checked.stats.cacheHits, 10);
  assert.equal(countProofDagTree(dag), 2_047);
  assert.throws(() => checkProofDag(kernel, { ...dag, digest: "forged" }), KernelError);
});

test("default kernel checking executes shared proof objects once", () => {
  const { kernel } = buildArithmeticSuite();
  let proof: Proof = refl(app("zero"));
  for (let depth = 0; depth < 20; depth += 1) proof = congr("pair", proof, proof);
  const checked = kernel.checkProofWithStats(proof);
  assert.equal(checked.stats.nodesVisited, 21);
  assert.equal(checked.stats.cacheHits, 20);
  assert.equal(checked.formula.tag, "eq");
  // The public admission path uses the same cached machine.
  assert.equal(kernel.checkProof(proof).tag, "eq");
  assert.equal(Object.isFrozen(proof), true);
});

test("incrementally cached proof certificates are immutable", () => {
  const { kernel } = buildArithmeticSuite();
  const proof = refl(app("zero"));
  kernel.checkProof(proof);
  assert.throws(() => {
    (proof as { rule: string }).rule = "axiom";
  }, TypeError);
  assert.equal(kernel.checkProof(proof).tag, "eq");
});

test("contextual proof caching remains safe when an assumption array is reused", () => {
  const { kernel } = buildArithmeticSuite();
  const proposition = pred("Nat", v("x"));
  const assumptions = [proposition];
  const proof = assume(proposition);
  assert.equal(kernel.checkProof(proof, assumptions), proposition);
  assumptions[0] = eq(v("x"), v("x"));
  assert.throws(() => kernel.checkProof(proof, assumptions), /active assumption/);
});

test("shared-proof caching remains sensitive to the assumption context", () => {
  const { kernel } = buildArithmeticSuite();
  const proposition = pred("Nat", v("x"));
  const shared = assume(proposition);
  const invalid = impElim(impIntro(proposition, shared), shared);
  assert.throws(() => checkProofDag(kernel, encodeProofDag(invalid)), /active assumption/);
});

test("proof cache keeps primary and secondary assumption contexts separate", () => {
  const kernel = createZfgKernel();
  const proposition = pred("Nat", v("x"));
  const extra = eq(v("x"), v("x"));
  const proof = assume(proposition);
  assert.equal(kernel.checkProof(proof, [proposition]), proposition);
  assert.equal(kernel.checkProof(proof, [extra, proposition]), proposition);
  assert.equal(kernel.checkProof(proof, [proposition, extra]), proposition);
  assert.throws(() => kernel.checkProof(proof, [extra]), /active assumption/);
  assert.throws(() => kernel.checkProof(proof), /active assumption/);
  assert.equal(kernel.checkProof(proof, [proposition]), proposition);
  assert.equal(kernel.checkProof(proof, [extra, proposition]), proposition);
});


test("DAG encoding traverses a deeply shared proof once per object", { timeout: 5_000 }, () => {
  let proof: Proof = refl(app("zero"));
  for (let depth = 0; depth < 40; depth += 1) proof = congr("pair", proof, proof);
  const dag = encodeProofDag(proof);
  assert.equal(dag.nodes.length, 41);
  assert.equal(dag.root, 40);
  assert.equal(countProofDagTree(dag), 2 ** 41 - 1);
});
