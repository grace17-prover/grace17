// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import {
  andElimLeft, app, axiom, callNative, callNativeNat, compileProofMachine, createZfgKernel, elaborateModule,
  exportTheorem, loadModuleGraph, proveRefinement, verifyProofMachine,
} from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const data = fileURLToPath(new URL("../lib/Grace/Core/Data.g17", import.meta.url));

test("declares set-encoded ADTs and executes generic structural recursion", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [data], [root]);
  const list = kernel.datatypes.get("Grace.Core.Data.List.inductive")!;
  assert.equal(list.predicate, "Grace.Core.Data.List");
  assert.deepEqual(list.parameters, ["A"]);
  assert.equal(list.setTheoreticEncoding, true);
  assert.deepEqual(list.constructors.map(item => [item.name, item.recursiveFields]), [
    ["Grace.Core.Data.List.nil", []],
    ["Grace.Core.Data.List.cons", [1]],
  ]);
  const declaration = kernel.definitions.get("Grace.Core.Data.List.inductive")!;
  assert.equal(declaration.properties.has("representation.nil"), true);
  assert.equal(declaration.properties.has("representation.cons"), true);
  assert.equal(declaration.properties.has("constructor.cons"), true);
  assert.equal(declaration.properties.has("injective.cons"), true);
  assert.equal(declaration.properties.has("disjoint.nil.cons"), true);
  assert.equal(declaration.properties.has("cases"), true);

  const xs = app("Grace.Core.Data.List.cons", app("empty"),
    app("Grace.Core.Data.List.cons", app("empty"), app("Grace.Core.Data.List.nil")));
  const omega = app("omega");
  const typing = proveRefinement(kernel, xs, "Grace.Core.Data.List", [omega], [], [andElimLeft(axiom("set.infinity"))]);
  assert.ok(typing);
  kernel.checkProof(typing!);
  assert.equal(callNativeNat(kernel, "Grace.Core.Data.ListOps.length", [omega, xs]), 2n);
  const mirrored = callNative(kernel, "Grace.Core.Data.TreeOps.mirror", [
    omega,
    { tag: "app", fn: "Grace.Core.Data.Tree.node", args: [
      { tag: "app", fn: "Grace.Core.Data.Tree.leaf", args: [1n] },
      { tag: "app", fn: "Grace.Core.Data.Tree.leaf", args: [2n] },
    ] },
  ]).value;
  assert.deepEqual(mirrored, { tag: "app", fn: "Grace.Core.Data.Tree.node", args: [
    { tag: "app", fn: "Grace.Core.Data.Tree.leaf", args: [2n] },
    { tag: "app", fn: "Grace.Core.Data.Tree.leaf", args: [1n] },
  ] });
  kernel.checkProof(kernel.theoremProofs.get("Grace.Core.Data.TreeOps.mirror.involutive")!);
  verifyProofMachine(kernel, compileProofMachine(exportTheorem(kernel, "Grace.Core.Data.TreeOps.mirror.involutive")));
  const computation = exportTheorem(kernel, "Grace.Core.Data.ListOps.length.two");
  assert.equal(computation.proof.nodes.length, 1);
  assert.equal(computation.proof.nodes[0]!.payload.rule, "compute");

  const principles = elaborateModule(kernel, `
module DataPrinciples
namespace DataPrinciples
import Grace.Core.Data
open Grace.Core.Data.List

lemma cons.injective (x xs y ys : Set)
  requires h : cons(x, xs) = cons(y, ys)
  shows x = y and xs = ys
proof
  settle with inductive.injective.cons

lemma nil.not_cons (x xs : Set)
  shows not (nil = cons(x, xs))
proof
  settle with inductive.disjoint.nil.cons

lemma exhaust (A : Set, xs : Grace.Core.Data.List(A))
  shows xs = nil or exists head, exists tail, (head in A and Grace.Core.Data.List(A, tail)) and xs = cons(head, tail)
proof
  settle with inductive.cases

end DataPrinciples
`);
  assert.deepEqual(principles.theorems, [
    "DataPrinciples.cons.injective", "DataPrinciples.nil.not_cons", "DataPrinciples.exhaust",
  ]);
});

test("rejects non-decreasing recursion over a user datatype", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
datatype Chain
  | done
  | next(rest : self)

define loop (xs : Chain) -> Chain
  | Chain.done => Chain.done
  | Chain.next(rest) => loop(Chain.next(rest))
`), /not on a structurally smaller value/);
});
