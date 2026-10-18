// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  app, assume, createZfgKernel, elaborateModule, eq, formulaEquals, instanceReport,
  pred, prepareInstanceProver, v, type Formula, type Proof, type Term,
} from "../src/index.ts";

test("multi-premise evidence has bounded checker entry calls and independently replays", () => {
  const kernel = createZfgKernel();
  const names = Array.from({ length: 24 }, (_, i) => `P${i}`);
  elaborateModule(kernel, `module EvidenceBatch
namespace EvidenceBatch
${names.map(name => `predicate ${name} (x : Set) := x = x`).join("\n")}
predicate Ready (x y : Set) := x = x
instance ready (x : Set)
${names.map((name, i) => `  requires h${i} : ${name}(x)`).join("\n")}
  shows Ready(x, pair(x, x))
proof
  unfold Ready
  rfl
end EvidenceBatch
`);
  const x = v("x");
  const assumptions = names.map(name => pred(`EvidenceBatch.${name}`, x));
  const registry = new Set(instanceReport(kernel).map(item => item.name));
  const prover = prepareInstanceProver(kernel, registry, assumptions);
  const original = kernel.checkProof.bind(kernel);
  let entries = 0;
  kernel.checkProof = (proof, context = []) => { entries++; return original(proof, context); };
  const result = prover.resolve("EvidenceBatch.Ready", [x, undefined]);
  assert.ok(result);
  assert.ok(entries <= 2, `24 premises caused ${entries} checker entries`);
  const wanted = pred("EvidenceBatch.Ready", x, app("pair", x, x));
  assert.ok(formulaEquals(kernel.checkProofWithStats(result.proof, assumptions).formula, wanted));
  assert.throws(() => kernel.checkProofWithStats(result.proof, assumptions.slice(1)));
  kernel.checkProof = original;
  const missing = prepareInstanceProver(kernel, registry, assumptions.slice(1));
  assert.equal(missing.resolve("EvidenceBatch.Ready", [x, undefined]), undefined);
  const concrete = prepareInstanceProver(kernel, registry, assumptions);
  entries = 0;
  kernel.checkProof = (proof, context = []) => { entries++; return original(proof, context); };
  const concreteProof = concrete.prove(app("pair", x, x), "EvidenceBatch.Ready", [x]);
  assert.ok(concreteProof);
  assert.ok(entries <= 2, `concrete query caused ${entries} checker entries`);
  assert.ok(formulaEquals(kernel.checkProofWithStats(concreteProof, assumptions).formula, wanted));
});

test("unchanged context reuse still detects mutation, replacement, and restoration", () => {
  const kernel = createZfgKernel();
  const p = eq(v("x"), v("y"));
  const q = eq(v("x"), v("z"));
  const context: Formula[] = [p];
  const proof = assume(p);
  for (let i = 0; i < 5; i++) assert.ok(formulaEquals(kernel.checkProof(proof, context), p));
  context[0] = q;
  assert.throws(() => kernel.checkProof(proof, context));
  context[0] = p;
  assert.ok(formulaEquals(kernel.checkProof(proof, context), p));
  context.length = 0;
  assert.throws(() => kernel.checkProof(proof, context));
  assert.throws(() => kernel.checkProof(proof));
  assert.throws(() => kernel.addTheorem("must_not_admit", p, proof));
  assert.equal(kernel.theorems.has("must_not_admit"), false);
  context.push(p);
  assert.ok(formulaEquals(kernel.checkProof(proof, context), p));
});

test("checker freezing remains deep for shallow-frozen certificates and shared cycles", () => {
  const kernel = createZfgKernel();
  const term = { tag: "var", name: "x" } as Term;
  const proof = { rule: "refl", term } as Proof & { metadata?: unknown };
  const metadata: { self?: unknown; term: Term } = { term };
  metadata.self = metadata;
  proof.metadata = metadata;
  Object.freeze(proof);
  kernel.checkProof(proof);
  assert.equal(Object.isFrozen(term), true);
  assert.equal(Object.isFrozen(metadata), true);
  assert.throws(() => { (term as { name: string }).name = "y"; });
  assert.ok(formulaEquals(kernel.checkProof(proof), eq(v("x"), v("x"))));
});


test("context snapshots deeply freeze separately allocated mutable assumptions", () => {
  const kernel = createZfgKernel();
  const right = { tag: "var" as const, name: "y" };
  const raw = { tag: "eq" as const, left: { tag: "var" as const, name: "x" }, right };
  const context: Formula[] = [raw];
  const proof = assume(eq(v("x"), v("y")));
  kernel.checkProof(proof, context);
  assert.equal(Object.isFrozen(context), false);
  assert.equal(Object.isFrozen(raw), true);
  assert.equal(Object.isFrozen(right), true);
  assert.throws(() => { right.name = "z"; });
  context[0] = eq(v("x"), v("z"));
  assert.throws(() => kernel.checkProof(proof, context));
});
