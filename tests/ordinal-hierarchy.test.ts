// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import {
  SurfaceError, app, canonical, classReport, createZfgKernel, elaborateModule, exportTheorem,
  loadModuleGraph, type Term,
} from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const setLibrary = fileURLToPath(new URL("../lib/Grace/Cumulus/Set.g17", import.meta.url));

const numeral = (value: number): Term => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};

test("von Neumann ordinal laws are checked and feed the Tau index", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  for (const name of [
    "Grace.Cumulus.Set.Ordinal.Ordinal.empty",
    "Grace.Cumulus.Set.Ordinal.Ordinal.next",
    "Grace.Cumulus.Set.Ordinal.Ordinal.member",
    "Grace.Cumulus.Set.Ordinal.Ordinal.natural",
    "Grace.Cumulus.Set.Ordinal.Ordinal.trichotomy",
    "Grace.Cumulus.Set.Ordinal.Ordinal.cases",
    "Grace.Cumulus.Set.Ordinal.Ordinal.subset_bound",
  ]) assert.ok(kernel.theorems.has(name), name);
  const trichotomy = exportTheorem(kernel, "Grace.Cumulus.Set.Ordinal.Ordinal.trichotomy");
  assert.equal(trichotomy.tactics?.steps.filter(step => step.command.includes("using membership")).length, 2,
    "nested derived membership inductions retain distinct hidden binders");
  kernel.checkProof(kernel.theoremProofs.get("Grace.Cumulus.Set.Ordinal.Ordinal.trichotomy")!);
  assert.equal(kernel.predicates.has("Ordinal"), false, "there is no opaque primitive Ordinal predicate");
  assert.equal(kernel.predicates.has("Grace.Cumulus.Set.Ordinal.Ordinal"), true);
});

test("finite cumulative stages compute to iterated powersets", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  const finite = "Grace.Cumulus.Set.Hierarchy.finite";
  const value = kernel.evaluateFast(app(finite, numeral(3)));
  const expected = app("powerset", app("powerset", app("powerset", app("empty"))));
  assert.equal(canonical(value), canonical(expected));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.finite.next_membership"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.finite.transitive"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.finite.subset_next"));
});

test("set-valued relation infrastructure is available without primitive relations", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  assert.equal(kernel.definitions.get("Grace.Cumulus.Set.Relation.product")?.kind, "separation");
  assert.equal(kernel.definitions.get("Grace.Cumulus.Set.Relation.domain")?.kind, "separation");
  assert.ok(kernel.definitions.get("Grace.Cumulus.Set.Relation.restrict")?.properties.has("membership"));
});

test("the cumulative hierarchy is a conservative noncomputable transfinite recursion", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  assert.equal(kernel.definitions.get("Grace.Cumulus.Set.Hierarchy.earlierValues")?.kind, "separation");
  assert.deepEqual(classReport(kernel).filter(item => item.name.includes("Set.Hierarchy")).map(item => item.name), [
    "Grace.Cumulus.Set.Hierarchy.CumulativeUniverse",
    "Grace.Cumulus.Set.Hierarchy.FiniteStage",
    "Grace.Cumulus.Set.Hierarchy.Ranked",
  ]);
  const hierarchy = kernel.definitions.get("Grace.Cumulus.Set.Hierarchy.V");
  assert.equal(hierarchy?.kind, "transfinite-recursive");
  assert.deepEqual([...hierarchy?.properties.keys() ?? []], [
    "history.membership", "equation.zero", "equation.successor", "equation.limit", "outside",
  ]);
  assert.equal(kernel.recursiveFunctions.has("Grace.Cumulus.Set.Hierarchy.V"), false,
    "transfinite class recursion is deliberately not executable");
  const rank = kernel.definitions.get("Grace.Cumulus.Set.Hierarchy.rank");
  assert.equal(rank?.kind, "membership-recursive");
  assert.deepEqual([...rank?.properties.keys() ?? []], ["history.membership", "equation"]);
  assert.equal(kernel.recursiveFunctions.has("Grace.Cumulus.Set.Hierarchy.rank"), false,
    "class-wide membership recursion is deliberately not executable");
  assert.equal(kernel.definitions.get("Grace.Cumulus.Set.Foundation.layers")?.kind, "replacement");
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Foundation.closure.transitive"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Foundation.membership.irreflexive"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.ordinal"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.member"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.empty"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.singleton"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.pair"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.rank.membership"));
  const rankOrdinal = exportTheorem(kernel, "Grace.Cumulus.Set.Hierarchy.rank.ordinal");
  assert.ok(rankOrdinal.dependencies.axioms.includes("set.foundation"));
  assert.ok(rankOrdinal.dependencies.theorems.includes(
    "Grace.Cumulus.Set.Foundation.membershipOn.wellFounded"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.zero"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.next"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.limit"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.limit_membership"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.transitive"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.V.monotone"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.CumulativeUniverse.membership"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.CumulativeUniverse.eq_Universe_of_rank"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Hierarchy.CumulativeUniverse.eq_Universe"));
  assert.deepEqual(kernel.foundationReport().schemaInstances.transfiniteRecursion,
    ["Grace.Cumulus.Set.Hierarchy.V"]);
  assert.deepEqual(kernel.foundationReport().schemaInstances.membershipRecursion,
    ["Grace.Cumulus.Set.Hierarchy.rank"]);
});

test("transfinite recursion rejects a counterfeit ordinal interface", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  assert.throws(() => elaborateModule(kernel, `module Counterfeit.Ordinal
namespace Counterfeit.Ordinal
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Basic.Set
open Grace.Cumulus.Set.Relation
class Ordinal (x : Set) := { x | x = x }
def next (x : Set) : Set := union2(x, singleton(x))
predicate Limit (x : Set) := x = x
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => bad beta
  | limit lambda => ⋃ { bad beta | beta < lambda }

end Counterfeit.Ordinal
`), (error: unknown) => error instanceof SurfaceError && /not definitionally the von Neumann ordinals/.test(error.message));
});

test("a general limit clause may refer to its clause-local ordinal binder", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  elaborateModule(kernel, `module General.LimitBinder
namespace General.LimitBinder
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
noncomputable transfinite def W (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => W beta
  | limit lambda => lambda

end General.LimitBinder
`);
  const definition = kernel.definitions.get("General.LimitBinder.W");
  assert.equal(definition?.kind, "transfinite-recursive");
  assert.ok(definition?.properties.has("equation.limit"));
});

test("transfinite recursion rejects counterfeit limit and successor interfaces", () => {
  const badLimit = createZfgKernel();
  loadModuleGraph(badLimit, [setLibrary], [root]);
  assert.throws(() => elaborateModule(badLimit, `module Counterfeit.Limit
namespace Counterfeit.Limit
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
predicate Limit (x : Set) := x = x
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => bad beta
  | limit lambda => lambda

end Counterfeit.Limit
`), /not definitionally the standard limit-ordinal predicate/);

  const badSuccessor = createZfgKernel();
  loadModuleGraph(badSuccessor, [setLibrary], [root]);
  assert.throws(() => elaborateModule(badSuccessor, `module Counterfeit.Successor
namespace Counterfeit.Successor
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
def next (x : Set) : Set := empty
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => bad beta
  | limit lambda => lambda

end Counterfeit.Successor
`), /is not definitionally α ∪ \{α\}/);
});

test("transfinite clauses enforce recursion position and fixed parameters", () => {
  const rejects = (source: string, pattern: RegExp) => {
    const kernel = createZfgKernel();
    loadModuleGraph(kernel, [setLibrary], [root]);
    assert.throws(() => elaborateModule(kernel, source), pattern);
  };
  rejects(`module Bad.ZeroRecursion
namespace Bad.ZeroRecursion
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => bad(0)
  | succ beta => bad beta
  | limit lambda => lambda

end Bad.ZeroRecursion
`, /may recur only in its successor clause/);
  rejects(`module Bad.LimitRecursion
namespace Bad.LimitRecursion
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => bad beta
  | limit lambda => bad(lambda)

end Bad.LimitRecursion
`, /may recur only in its successor clause/);
  rejects(`module Bad.SuccessorRecursion
namespace Bad.SuccessorRecursion
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
noncomputable transfinite def bad (alpha : Ordinal) : Set
  | 0 => empty
  | succ beta => bad(next(beta))
  | limit lambda => lambda

end Bad.SuccessorRecursion
`, /must call the immediately preceding ordinal/);
  rejects(`module Bad.ParameterRecursion
namespace Bad.ParameterRecursion
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
noncomputable transfinite def bad (A : Set, alpha : Ordinal) : Set
  | 0 => A
  | succ beta => bad(empty, beta)
  | limit lambda => lambda

end Bad.ParameterRecursion
`, /must call the immediately preceding ordinal/);
});

test("foundation recursion exposes only a checked member-history graph", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  assert.throws(() => elaborateModule(kernel, `module Bad.FoundationScope
namespace Bad.FoundationScope
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Ordinal
open Grace.Cumulus.Set.Relation
noncomputable foundation def bad (x : Set) : Set
  | x using history => pair(history, escaped)

end Bad.FoundationScope
`), /unknown variable or constant escaped/i);
  assert.throws(() => elaborateModule(kernel, `module Bad.FoundationShape
namespace Bad.FoundationShape
import Grace.Cumulus.Set
noncomputable foundation def bad (x : Set) : Set
  | x => empty

end Bad.FoundationShape
`), /expected `\| x using history => step`/);
});

test("set-sized well-founded recursion accepts an ordinary checked certificate", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  const result = elaborateModule(kernel, `module General.WellFounded
namespace General.WellFounded
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Foundation
noncomputable well-founded def rankOn (A x : Set) : Set
  over A ordered by membershipOn(A)
  certified by membershipOn.wellFounded
  | x using history => 𝒫(history)

end General.WellFounded
`);
  assert.ok(result.definitions.includes("General.WellFounded.rankOn"));
  const definition = kernel.definitions.get("General.WellFounded.rankOn");
  assert.equal(definition?.kind, "well-founded-set-recursive");
  assert.deepEqual([...definition?.properties.keys() ?? []], [
    "wellFounded", "solution.existsUnique", "history.membership", "value", "equation", "equation.direct", "outside",
  ]);
  assert.equal(kernel.recursiveFunctions.has("General.WellFounded.rankOn"), false,
    "set-sized well-founded recursion is deliberately non-executable");
  assert.throws(() => elaborateModule(kernel, `module General.BadCertificate
namespace General.BadCertificate
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Foundation
noncomputable well-founded def bad (A x : Set) : Set
  over A ordered by membershipOn(A)
  certified by membershipOn.relation
  | x using history => history

end General.BadCertificate
`), /must prove wellFoundedOn/);
});

test("surface proofs expose checked induction over an arbitrary well-founded relation", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [setLibrary], [root]);
  const result = elaborateModule(kernel, `module General.WellFoundedInduction
namespace General.WellFoundedInduction
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Foundation
theorem reflexive (A r : Set)
  requires founded : wellFoundedOn(r, A)
  shows ∀ x, x ∈ A → x = x
proof
  induction x over A ordered by r certified by founded
  intro x
  intro hx
  intro ih
  rfl

end General.WellFoundedInduction
`);
  assert.ok(result.theorems.includes("General.WellFoundedInduction.reflexive"));
  const theorem = exportTheorem(kernel, "General.WellFoundedInduction.reflexive");
  assert.equal(theorem.tactics?.steps[0]?.command,
    "induction x over A ordered by r certified by founded");
  kernel.checkProof(kernel.theoremProofs.get("General.WellFoundedInduction.reflexive")!);
});
