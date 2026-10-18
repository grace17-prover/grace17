// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import assert from "node:assert/strict";
import test from "node:test";
import { fileURLToPath } from "node:url";
import {
  and, andIntro, app, assume, axiom, bind, canonical, compileDenseKernelModule, compileKernelModule,
  compileSeparateKernelModule, compileSeparateKernelModuleOverClosure, createZfKernel, createZfgKernel, ctor, decodeCompiledKernelModule,
  decodeDenseKernelModule, decodeSeparateKernelModule, decodeSurfaceEnvironmentIndex, definition, elaborateModule,
  encodeCompiledKernelModule, encodeDenseKernelModule, encodeProofDag, encodeSeparateKernelModule,
  encodeSurfaceEnvironmentIndex, eq, existsIntro, exportSurfaceEnvironmentIndex, forall,
  forallElim, forallIntro, imp, impIntro, loadModuleGraph, pred, refl, replayCompiledKernelModule, replayDenseKernelModule,
  replaySeparateKernelModule, replaySeparateKernelModuleExact, installSurfaceEnvironmentIndex,
  substituteFormula, v,
  theorem, type CompiledKernelModule, type DenseCompiledKernelModule, type SeparateCompiledKernelModule,
} from "../src/index.ts";
import { sha256Hex } from "../src/hash.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));
// The default graph is two modules whose closure exercises every admission
// kind (subsets, replacements, transfinite and membership recursion) in a
// few seconds. G17_FULL_REPLAY=1 replays the complete Cumulus library, which
// needs several gigabytes and minutes rather than seconds.
const roots = process.env.G17_FULL_REPLAY
  ? [fileURLToPath(new URL("../lib/Grace/Cumulus.g17", import.meta.url))]
  : [
    fileURLToPath(new URL("../lib/Grace/Cumulus/Set/Hierarchy.g17", import.meta.url)),
    fileURLToPath(new URL("../lib/Grace/Cumulus/Cardinal/Finite.g17", import.meta.url)),
  ];

function redigest(value: Omit<CompiledKernelModule, "digest">): CompiledKernelModule {
  return { ...value, digest: sha256Hex(canonical(value)) };
}

let cached: {
  readonly base: ReturnType<typeof createZfgKernel>;
  readonly source: ReturnType<typeof createZfgKernel>;
  readonly compiled: CompiledKernelModule;
  readonly dense: DenseCompiledKernelModule;
} | undefined;
function fixture() {
  if (cached) return cached;
  const base = createZfgKernel();
  const source = base.fork();
  const checkpoint = source.admissionCheckpoint();
  loadModuleGraph(source, roots, [library]);
  // Each format still exercises the whole graph. Do not retain the unused
  // representation while constructing, decoding and replaying the other one.
  let compiled: CompiledKernelModule | undefined;
  let dense: DenseCompiledKernelModule | undefined;
  return cached = {
    base, source,
    get compiled() {
      dense = undefined;
      return compiled ??= compileKernelModule(source, checkpoint, { module: "Grace.Cumulus" });
    },
    get dense() {
      compiled = undefined;
      return dense ??= compileDenseKernelModule(base, source, checkpoint, { module: "Grace.Cumulus" });
    },
  };
}

test("G17C replays the complete admission stream of a module graph from ZFG", () => {
  const { source, compiled } = fixture();
  const decoded = decodeCompiledKernelModule(encodeCompiledKernelModule(compiled));
  const replayed = replayCompiledKernelModule(createZfgKernel(), decoded);

  assert.equal(replayed.digest(), source.digest());
  assert.equal(replayed.theorems.size, source.theorems.size);
  assert.equal(replayed.definitions.size, source.definitions.size);
  assert.ok(compiled.events.some(event => event.operation === "defineSubset"));
  assert.ok(compiled.events.some(event => event.operation === "defineReplacement"));
  assert.ok(compiled.events.some(event => event.operation === "defineTransfiniteFunction"));
  assert.ok(compiled.events.some(event => event.operation === "defineMembershipRecursiveFunction"));
});

test("G17C rejects corruption and leaves the base unchanged", () => {
  const { compiled } = fixture();
  const bytes = encodeCompiledKernelModule(compiled);
  bytes[bytes.length - 2] ^= 1;
  assert.throws(() => decodeCompiledKernelModule(bytes), /compiled module|Malformed compiled module encoding/);

  const base = createZfKernel();
  const before = base.digest();
  assert.throws(() => replayCompiledKernelModule(base, compiled), /different base environment/);
  assert.equal(base.digest(), before);
});

test("a redigested false theorem event is still rejected by the kernel", () => {
  const { compiled } = fixture();
  const theoremIndex = compiled.events.findIndex(event => event.operation === "addTheorem");
  assert.notEqual(theoremIndex, -1);
  const oldEvent = compiled.events[theoremIndex]!;
  const oldPayload = oldEvent.payload as Record<string, unknown>;
  const events = [...compiled.events];
  events[theoremIndex] = {
    operation: "addTheorem",
    payload: { ...oldPayload, proof: { $grace17ProofDag: encodeProofDag(axiom("set.empty")) } },
  };
  const { digest: _digest, ...body } = compiled;
  const forged = redigest({ ...body, events });
  const base = createZfgKernel();
  const before = base.digest();
  assert.throws(() => replayCompiledKernelModule(base, forged), /derives .* expected|wrong conclusion/);
  assert.equal(base.digest(), before);
});

test("G17C preserves proof-bearing conservative and well-founded definitions", () => {
  const source = createZfgKernel();
  source.defineFunction("embed", ["x"], app("singleton", v("x")));
  const closure = forall("x", imp(pred("in", v("x"), app("omega")),
    pred("in", app("embed", v("x")), app("powerset", app("omega")))));
  source.addAxiom("embed.closure", closure);
  const order = app("epsilon0.less");
  const domain = app("epsilon0");
  source.addAxiom("e0.well_founded", pred("wellFoundedOn", order, domain));
  source.addAxiom("nat.in_e0", forall("x", pred("in", v("x"), domain)));
  source.addAxiom("nat.predecessor_descends", forall("n", pred("relates", order, v("n"), app("succ", v("n")))));
  const replayBase = source.fork();
  const checkpoint = source.admissionCheckpoint();
  const relation = eq(v("value"), v("x"));
  const uniquenessPremise = eq(v("other"), v("x"));
  const existsUnique = forallIntro("x", existsIntro("value", and(
    relation,
    forall("other", imp(substituteFormula(relation, "value", v("other")), eq(v("other"), v("value")))),
  ), v("x"), andIntro(refl(v("x")), forallIntro("other", impIntro(uniquenessPremise, assume(uniquenessPremise))))));
  source.defineUniqueFunction({ name: "selected", parameters: ["x"], value: "value", relation, existsUnique });

  const domainSubset = forall("member", imp(pred("in", v("member"), v("subset")), pred("in", v("member"), v("A"))));
  source.defineWellFoundedSetFunction({
    name: "rankOn", parameters: ["A"], variable: "x", predecessor: "y", history: "h", domain: v("A"),
    precedes: pred("in", v("y"), v("x")), step: app("powerset", v("h")),
    wellFounded: forallIntro("A", forallIntro("subset", impIntro(domainSubset,
      forallElim(axiom("set.foundation"), v("subset"))))),
  });

  source.reifyUnaryOperation({
    name: "Embed", operation: "embed", domain: app("omega"), codomain: app("powerset", app("omega")),
    variable: "x", closure: axiom("embed.closure"),
  });

  source.defineWellFoundedFunction({
    name: "countdown", parameters: ["x"], coverageDatatype: "Naturals", coverageParameter: 0,
    relation: order, domain, measure: v("x"), wellFounded: axiom("e0.well_founded"),
    measureInDomain: axiom("nat.in_e0"), decreases: [axiom("nat.predecessor_descends")], equations: [
      { patterns: [ctor("zero")], body: app("zero") },
      { patterns: [ctor("succ", bind("n"))], body: app("countdown", v("n")) },
    ],
  });

  const compiled = compileKernelModule(source, checkpoint, { module: "CertificateCoverage" });
  const replayed = replayCompiledKernelModule(replayBase,
    decodeCompiledKernelModule(encodeCompiledKernelModule(compiled)));
  assert.equal(replayed.digest(), source.digest());
  assert.deepEqual(compiled.events.map(event => event.operation), [
    "defineUniqueFunction", "defineWellFoundedSetFunction", "reifyUnaryOperation", "defineWellFoundedFunction",
  ]);
});

test("G17C refuses to compile a library interval that increases axiomatic strength", () => {
  const source = createZfgKernel();
  const checkpoint = source.admissionCheckpoint();
  source.addAxiom("forbidden.library.axiom", eq(app("empty"), app("omega")));
  assert.throws(() => compileKernelModule(source, checkpoint, { module: "UnsoundLibrary" }),
    /may not introduce axioms/);
});

test("G17C modules compose only over their exact admitted dependency prefix", () => {
  const source = createZfgKernel();
  const beforeA = source.admissionCheckpoint();
  source.defineFunction("identity", ["x"], v("x"));
  const moduleA = compileKernelModule(source, beforeA, { module: "A" });
  const beforeB = source.admissionCheckpoint();
  const statement = forall("x", eq(app("identity", v("x")), v("x")));
  source.addTheorem("identity.equation", statement, definition("identity"));
  const moduleB = compileKernelModule(source, beforeB, {
    module: "B", dependencies: [{ module: "A", digest: moduleA.digest }],
  });

  const base = createZfgKernel();
  assert.throws(() => replayCompiledKernelModule(base, moduleB), /different base environment/);
  const withA = replayCompiledKernelModule(base, moduleA);
  const withB = replayCompiledKernelModule(withA, moduleB);
  assert.equal(withB.digest(), source.digest());
});

test("dense G17C theorem batches replay a module graph at the exact digest", () => {
  const { source, dense } = fixture();
  const decoded = decodeDenseKernelModule(encodeDenseKernelModule(dense));
  const replayed = replayDenseKernelModule(createZfgKernel(), decoded);
  assert.equal(replayed.digest(), source.digest());
  assert.ok(dense.events.some(event => event.kind === "theoremBatch"));
  assert.ok(dense.events.some(event => event.kind === "admission" && event.event.operation === "defineTransfiniteFunction"));
});

test("dense G17C checks theorem statements rather than trusting batch boundaries", () => {
  const { dense } = fixture();
  const index = dense.events.findIndex(event => event.kind === "theoremBatch");
  assert.notEqual(index, -1);
  const batch = dense.events[index]!;
  assert.equal(batch.kind, "theoremBatch");
  const events = [...dense.events];
  events[index] = {
    ...batch,
    statements: [{ ...batch.statements[0]!, statement: eq(app("empty"), app("omega")) }, ...batch.statements.slice(1)],
  };
  const { digest: _digest, ...body } = dense;
  const forged = { ...body, events, digest: sha256Hex(canonical({ ...body, events })) } as DenseCompiledKernelModule;
  const base = createZfgKernel();
  const before = base.digest();
  assert.throws(() => replayDenseKernelModule(base, forged), /boundary mismatch/);
  assert.equal(base.digest(), before);
});

test("dense G17C preserves theorem availability across definition boundaries", () => {
  const base = createZfgKernel();
  const source = base.fork();
  const checkpoint = source.admissionCheckpoint();
  const first = forall("x", eq(v("x"), v("x")));
  source.addTheorem("first", first, forallIntro("x", refl(v("x"))));
  source.defineFunction("identityAfterFirst", ["x"], v("x"));
  source.addTheorem("second", first, theorem("first"));
  const dense = compileDenseKernelModule(base, source, checkpoint, { module: "Ordered" });
  assert.deepEqual(dense.events.map(event => event.kind), ["theoremBatch", "admission", "theoremBatch"]);
  assert.equal(replayDenseKernelModule(base, dense).digest(), source.digest());
});

test("separate G17C modules replay an exact ordered dependency prefix", () => {
  const foundation = createZfgKernel();
  const sourceA = foundation.fork();
  const beforeA = sourceA.admissionCheckpoint();
  sourceA.defineFunction("cachedIdentity", ["x"], v("x"));
  const moduleA = compileSeparateKernelModule(foundation, foundation, sourceA, beforeA, { module: "Cache.A" });
  const checkedA = replaySeparateKernelModuleExact(foundation,
    decodeSeparateKernelModule(encodeSeparateKernelModule(moduleA)));
  assert.equal(checkedA.checkedModuleReceipt("Cache.A"), moduleA.digest);

  const sourceB = checkedA.fork();
  const beforeB = sourceB.admissionCheckpoint();
  const statement = forall("x", eq(app("cachedIdentity", v("x")), v("x")));
  sourceB.addTheorem("cachedIdentity.equation", statement, definition("cachedIdentity"));
  const dependencies = [{ module: "Cache.A", digest: moduleA.digest }];
  const moduleB = compileSeparateKernelModule(foundation, checkedA, sourceB, beforeB, {
    module: "Cache.B", dependencies,
  });
  assert.throws(() => replaySeparateKernelModuleExact(foundation, moduleB), /dependency Cache.A/);
  const checkedB = replaySeparateKernelModuleExact(checkedA, moduleB);
  assert.equal(checkedB.digest(), sourceB.digest());
  assert.equal(checkedB.checkedModuleReceipt("Cache.B"), moduleB.digest);
});

test("receipt replay permits unrelated monotone declarations but still checks every event", () => {
  const foundation = createZfgKernel();
  const source = foundation.fork();
  const checkpoint = source.admissionCheckpoint();
  source.defineFunction("portableIdentity", ["x"], v("x"));
  const compiled = compileSeparateKernelModule(foundation, foundation, source, checkpoint, { module: "Portable" });

  const larger = foundation.fork();
  larger.defineFunction("unrelated", ["x"], app("singleton", v("x")));
  assert.throws(() => compileSeparateKernelModule(
    foundation, larger, larger, larger.admissionCheckpoint(), { module: "NotPortable" },
  ), /exact ordered dependency closure/);
  const replayed = replaySeparateKernelModule(larger, compiled);
  assert.equal(replayed.checkedModuleReceipt("Portable"), compiled.digest);
  assert.equal(replayed.functions.has("unrelated"), true);
  assert.equal(replayed.functions.has("portableIdentity"), true);
  assert.throws(() => replaySeparateKernelModuleExact(larger, compiled), /exact dependency prefix/);

  const theoremBatch = compiled.events.find(item => item.kind === "admission");
  assert.ok(theoremBatch);
  const { digest: _digest, ...body } = compiled;
  const forgedBody = { ...body, resultEnvironment: "0".repeat(64) };
  const forged = { ...forgedBody, digest: sha256Hex(canonical(forgedBody)) } as SeparateCompiledKernelModule;
  assert.throws(() => replaySeparateKernelModuleExact(foundation, forged), /wrong environment/);
});

test("surface-index sidecars restore notation, soft types, and tactic macros without trust", () => {
  const foundation = createZfgKernel();
  const source = foundation.fork();
  const checkpoint = source.admissionCheckpoint();
  elaborateModule(source, `module Cache.Surface
namespace Cache.Surface
namespace Public
predicate Same (x y : Set) := x = y
predicate Marked (x : Set) := x = x
notation infix 50 "≈" => Same
class Everything (x : Set) := { x | x = x }
tactic reflexive := settle with Same
instance marked (x : Set)
  shows Marked(x)
proof
  unfold Marked
  rfl
theorem distinct (x y : Set)
  requires apart : x ≠ y
  shows x ≠ y
proof
  exact apart
end Public
export open Cache.Surface.Public

end Cache.Surface
`);
  const compiled = compileSeparateKernelModule(foundation, foundation, source, checkpoint, { module: "Cache.Surface" });
  const index = exportSurfaceEnvironmentIndex(source, compiled.module, compiled.digest);
  const replayed = replaySeparateKernelModuleExact(foundation,
    decodeSeparateKernelModule(encodeSeparateKernelModule(compiled)));
  installSurfaceEnvironmentIndex(replayed,
    decodeSurfaceEnvironmentIndex(encodeSurfaceEnvironmentIndex(index)));

  const client = elaborateModule(replayed, `module Cache.Client
namespace Cache.Client
import Cache.Surface
lemma reflexive (x : Everything)
  shows x ≈ x
proof
  reflexive
lemma marked (x : Set)
  shows Marked(x)
proof
  synthesize

end Cache.Client
`);
  assert.deepEqual(client.theorems, ["Cache.Client.reflexive", "Cache.Client.marked"]);

  assert.equal(index.signatures.find(item => item.name === "Cache.Surface.Public.distinct")?.requirementCount, 1);
  elaborateModule(replayed, `module Cache.BoundaryClient
namespace Cache.BoundaryClient
import Cache.Surface
theorem distinct_client (x y : Set)
  requires apart : x ≠ y
  shows x ≠ y
proof
  exact distinct at x, y with *

end Cache.BoundaryClient
`);
  const forged = { ...index, signatures: index.signatures.map(item =>
    item.name === "Cache.Surface.Public.distinct" ? { ...item, requirementCount: 0 } : item) };
  const { digest: ignored, ...forgedBody } = forged;
  const altered = { ...forgedBody, digest: sha256Hex(canonical(forgedBody)) };
  const fresh = replaySeparateKernelModuleExact(foundation, compiled);
  installSurfaceEnvironmentIndex(fresh, altered);
  // A forged boundary may mislead elaboration, but cannot discharge a premise.
  assert.throws(() => elaborateModule(fresh, `module Cache.ForgedClient
namespace Cache.ForgedClient
import Cache.Surface
theorem unjustified (x y : Set)
  shows x ≠ y
proof
  exact distinct at x, y with *

end Cache.ForgedClient
`));
  for (const count of [-1, 0.5, Number.MAX_SAFE_INTEGER + 1]) {
    const bad = { ...index, signatures: index.signatures.map(item =>
      item.name === "Cache.Surface.Public.distinct" ? { ...item, requirementCount: count } : item) };
    const { digest, ...body } = bad;
    assert.throws(() => encodeSurfaceEnvironmentIndex({ ...body, digest: sha256Hex(canonical(body)) }),
      /surface-index contents/);
  }

  const bytes = encodeSurfaceEnvironmentIndex(index);
  bytes[bytes.length - 2] ^= 1;
  assert.throws(() => decodeSurfaceEnvironmentIndex(bytes), /surface[- ]index|encoding/i);
  assert.throws(() => installSurfaceEnvironmentIndex(foundation, index), /checked module receipt/);
});

test("surface-index restores shared namespace ownership and ambiguity independently of file names", () => {
  const foundation = createZfgKernel();
  const source = foundation.fork();
  const checkpoint = source.admissionCheckpoint();
  for (const side of ["Left", "Right"]) elaborateModule(source, `module Files.${side}
namespace _root_.Public.${side}
def value : Set := empty
end Public.${side}
namespace _root_.Shared
end Shared
`);
  const compiled = compileSeparateKernelModule(foundation, foundation, source, checkpoint, { module: "Files.Bundle" });
  const index = exportSurfaceEnvironmentIndex(source, compiled.module, compiled.digest);
  const replayed = replaySeparateKernelModuleExact(foundation, compiled);
  installSurfaceEnvironmentIndex(replayed, decodeSurfaceEnvironmentIndex(encodeSurfaceEnvironmentIndex(index)));
  assert.throws(() => elaborateModule(replayed, `module Hidden
open Shared
`), /unimported namespace/);
  elaborateModule(replayed, `module SharedClient
import Files.Left
open Shared
namespace _root_.Public.Left
theorem uses_value
  shows value = empty
proof
  unfold value
  rfl
end Public.Left
`);
  assert.throws(() => elaborateModule(replayed, `module AmbiguousClient
import Files.Left
import Files.Right
open Public.Left
open Public.Right
def result : Set := value
`), /ambiguous name value; qualify one of: Public.Left.value \(module Files.Left\), Public.Right.value \(module Files.Right\)/);
});

// A closure-based artifact names its whole import closure as a set, so a
// diamond of modules compiles and replays without a linear prefix order.
test("closure-based separate modules compile over a diamond and replay in any closure order", () => {
  const foundation = createZfgKernel();
  const define = (base: ReturnType<typeof createZfgKernel>, name: string) => {
    const completed = base.fork();
    completed.defineFunction(name, ["x"], v("x"));
    return completed;
  };
  const compile = (base: ReturnType<typeof createZfgKernel>, module: string, dependencies: SeparateCompiledKernelModule[]) => {
    const checkpoint = base.admissionCheckpoint();
    const completed = define(base, module.toLowerCase());
    return compileSeparateKernelModuleOverClosure(foundation, base, completed, checkpoint, {
      module, dependencies: dependencies.map(item => ({ module: item.module, digest: item.digest })),
    });
  };
  const moduleA = compile(foundation, "Diamond.A", []);
  const withA = replaySeparateKernelModule(foundation, moduleA);
  const moduleB = compile(withA, "Diamond.B", [moduleA]);
  const moduleC = compile(withA, "Diamond.C", [moduleA]);
  const withABC = replaySeparateKernelModule(replaySeparateKernelModule(withA, moduleB), moduleC);
  assert.throws(() => compileSeparateKernelModule(foundation, withABC, define(withABC, "d"), withABC.admissionCheckpoint(), {
    module: "Diamond.D", dependencies: [moduleA, moduleB, moduleC].map(item => ({ module: item.module, digest: item.digest })),
  }), /exact ordered dependency closure/);
  const moduleD = compile(withABC, "Diamond.D", [moduleA, moduleB, moduleC]);

  // The strict path accepts the closure replayed in the other order too.
  const withACB = replaySeparateKernelModule(replaySeparateKernelModule(withA, moduleC), moduleB);
  const checkedD = replaySeparateKernelModuleExact(withACB, moduleD);
  assert.equal(checkedD.functions.has("diamond.d"), true);
  assert.equal(checkedD.digest(), moduleD.resultEnvironment);
  assert.throws(() => replaySeparateKernelModuleExact(replaySeparateKernelModule(withA, moduleB), moduleD), /dependency Diamond.C/);

  // The compile base may carry no receipt outside the closure.
  assert.throws(() => compile(withABC, "Diamond.E", [moduleA, moduleB]), /exactly the dependency closure receipts/);
});

// The environment digest is the generic canonical serialization of the
// snapshot; the kernel's memoized serializer must agree with it exactly.
test("the environment digest equals the generic canonical serialization of the snapshot", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [fileURLToPath(new URL("../lib/Grace/Cumulus/Set/Hierarchy.g17", import.meta.url))], [library]);
  assert.equal(kernel.digest(), sha256Hex(canonical(kernel.environmentSnapshot())));
  const fork = kernel.fork();
  fork.defineFunction("digest.probe", ["x"], v("x"));
  assert.equal(fork.digest(), sha256Hex(canonical(fork.environmentSnapshot())));
});
