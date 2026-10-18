// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled topological and metric spaces: a space is a structure X with
// projections X.carrier and X.opens, a metric space one with X.carrier and
// X.dist; under a hypothesis TopologicalSpace(X) or MetricSpace(X) a binder
// (x : X) is membership in the carrier and u ⇝ x is convergence, continuity
// is the guard f : X ⇒ Y, openness of compound sets is synthesized, the
// rewrite sets close the textbook identities, and the flagship theorems are
// stated in their textbook form.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfgKernel, formulaEquals, loadModuleSourceGraph } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BundledTopology\nimport Grace.Cumulus.Topology.Spaces\nimport Grace.Cumulus.Metric.Spaces\n";

const section = (body: string) => header + `
section S
variable (X : Set)
hypothesis space : TopologicalSpace(X)
${body}
end S
`;

const metricSection = (body: string) => header + `
section M
variable (X : Set)
hypothesis metric : MetricSpace(X)
${body}
end M
`;

function load(source: string) {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledTopology.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledTopology.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

test("(x : X) is x ∈ X.carrier and u ⇝ x is Converges(X, u, x) under a space hypothesis", () => {
  const written = load(section(`
theorem limit (u : Set) (x : X)
  requires converges : u ⇝ x
  shows x ∈ X
proof
  exact Converges.limit_mem with *
`));
  const spelled = load(header + `
theorem limit (X u x : Set)
  requires xIn : x ∈ TopologicalSpace.carrier(X)
  requires space : TopologicalSpace(X)
  requires converges : Converges(X, u, x)
  shows x ∈ TopologicalSpace.carrier(X)
proof
  exact Converges.limit_mem with *
`);
  assert.ok(formulaEquals(written.theorems.get("BundledTopology.limit")!, spelled.theorems.get("BundledTopology.limit")!));
});

test("the uniqueness of limits prints with the carrier binders and ⇝", () => {
  const result = check(section(`
theorem unique (u : Set) (x y : X)
  requires hausdorff : Hausdorff(X)
  requires first : u ⇝ x
  requires second : u ⇝ y
  shows x = y
proof
  exact Converges.unique with *
`));
  const statement = result.theorems.find(item => item.name === "BundledTopology.unique")!.statement;
  assert.match(statement, /\(x y : X\)/u);
  assert.match(statement, /u ⇝ x → u ⇝ y → x = y$/u);
});

test("openness and closedness of compound sets are synthesized, and the rewrite set closes the interior and closure identities", () => {
  check(section(`
theorem meet (U V : Set)
  requires openU : Open(X, U)
  requires openV : Open(X, V)
  shows Open(X, U ∩ V ∩ X.carrier)
proof
  synthesize

theorem inner (A : Set)
  shows Open(X, interior(X, A))
proof
  synthesize

theorem outer (A : Set)
  requires hA : A ⊆ X
  shows Closed(X, closure(X, A) ∪ ∅)
proof
  synthesize

theorem simplified (A B : Set)
  shows interior(X, interior(X, A) ∩ interior(X, B)) = interior(X, A) ∩ interior(X, B)
proof
  topology_simp

theorem fixed (U : Set)
  requires open : Open(X, U)
  shows closure(X, interior(X, U)) = closure(X, U)
proof
  topology_simp
`));
});

test("the flagship theorems are stated in their textbook form", () => {
  check(header + `
theorem tube (X Y A B : Set)
  requires spaceX : TopologicalSpace(X)
  requires spaceY : TopologicalSpace(Y)
  requires compactA : Compact(X, A)
  requires compactB : Compact(Y, B)
  shows Compact(productSpace(X, Y), A × B)
proof
  exact Compact.prod with *

theorem heineBorel (A B : Real)
  requires ordered : A ≤ B
  shows Compact(realLine, closedInterval(A, B))
proof
  exact Compact.interval with *

theorem image (f X Y A : Set)
  requires continuous : f : X ⇒ Y
  requires compact : Compact(X, A)
  shows Compact(Y, functionImage(f, A, Y.carrier))
proof
  exact Compact.continuous_image with *

theorem closedCompact (X K : Set)
  requires space : TopologicalSpace(X)
  requires hausdorff : Hausdorff(X)
  requires compact : Compact(X, K)
  shows Closed(X, K)
proof
  exact Compact.closed_of_hausdorff with *
`);
});

test("a metric space supplies the carrier binder, real distances, the triangle inequality, and the metric rewrite set", () => {
  const result = check(metricSection(`
theorem triangle (x y z : X)
  shows d(x, z) ≤ d(x, y) + d(y, z)
proof
  exact dist_triangle with *

theorem real (x y : X)
  shows X.dist(x, y) ∈ ℝ
proof
  synthesize

theorem vanishing (x : X)
  shows d(x, x) = (0:R)
proof
  metric_simp

theorem limits (u : Set) (x y : X)
  requires first : u ⇝ x
  requires second : u ⇝ y
  shows x = y
proof
  exact Converges.unique_metric with *

theorem open (x : X) (r : Real)
  shows Open(metricTopology(X), ball(X, x, r))
proof
  synthesize
`));
  const triangle = result.theorems.find(item => item.name === "BundledTopology.triangle")!.statement;
  assert.match(triangle, /→ d\(x, z\) ≤ d\(x, y\) \+ d\(y, z\)$/u);
  assert.match(result.theorems.find(item => item.name === "BundledTopology.real")!.statement, /→ d\(x, y\) ∈ ℝ$/u);
});

test("ε–δ continuity is continuity of the metric topologies, and the bridges relate the bundled and unbundled forms", () => {
  check(header + `
theorem continuity (f X Y : Set)
  requires metricX : MetricSpace(X)
  requires metricY : MetricSpace(Y)
  shows MetricContinuous(f, X, Y) ↔ f : metricTopology(X) ⇒ metricTopology(Y)
proof
  exact MetricContinuous.iff_continuous with *

theorem bridge (A T : Set)
  requires topology : IsTopology(A, T)
  shows TopologicalSpace(TopologicalSpace.mk(A, T)) ∧
    TopologicalSpace.opens(TopologicalSpace.mk(A, T)) = T
proof
  constructor
  . exact TopologicalSpace.of_parts with topology
  . topology_projections

theorem metricBridge (A d : Set)
  requires metric : IsMetric(A, d)
  shows MetricSpace(MetricSpace.mk(A, d))
proof
  exact MetricSpace.of_parts with metric
`);
});

test("Compact(X) and Compact(X, A) coexist at two arities, resolved by arity and by the goal, and a bare apply discharges the section hypothesis", () => {
  const result = check(section(`
theorem whole
  requires compact : Compact(X)
  shows Compact(X, X.carrier)
proof
  have criterion := Compact.space_iff with space
  exact criterion.forward with compact

theorem unfolded
  requires compact : Compact(X)
  shows IsCompact(X.carrier, X.opens, X.carrier)
proof
  unfold Compact at compact
  exact compact

theorem applied (A : Set)
  requires compact : IsCompact(X.carrier, X.opens, A)
  shows Compact(X, A)
proof
  apply Compact.of_parts
  exact compact
`));
  const whole = result.theorems.find(item => item.name === "BundledTopology.whole")!.statement;
  assert.match(whole, /→ Compact\(X\) → Compact\(X, X\.carrier\)$/u);
  // Two declarations of one name at different arities in one module.
  const kernel = load(header + `
predicate Tiny (A : Set) := A = ∅
predicate Tiny (A B : Set) := A = ∅ ∧ B = ∅

theorem both (A B : Set)
  requires both : Tiny(A, B)
  shows Tiny(A) ∧ Tiny(B)
proof
  unfold Tiny at both
  constructor
  . unfold Tiny
    exact both.left
  . unfold Tiny
    exact both.right
`);
  assert.equal(kernel.predicates.get("BundledTopology.Tiny"), 1);
  assert.equal(kernel.predicates.get("BundledTopology.arity2.Tiny"), 2);
  // A premise that is not a section hypothesis stays a goal.
  assert.throws(() => load(section(`
theorem open (A : Set)
  shows Compact(X, A)
proof
  apply Compact.of_parts
`)), /1 goal remains|goal remains|unsolved/u);
});

test("a rewrite that ends its branch closes the goal it makes reflexive, and a rfl after it still closes it", () => {
  check(section(`
theorem rewritten (A B : Set)
  requires equal : A = B
  shows interior(X, A) = interior(X, B)
proof
  rw equal

theorem explicit (A B : Set)
  requires equal : A = B
  shows interior(X, A) = interior(X, B)
proof
  rw equal
  rfl

theorem bulleted (A B : Set)
  requires equal : A = B
  shows interior(X, A) = interior(X, B) ∧ closure(X, A) = closure(X, B)
proof
  constructor
  . rw equal
  . rw equal
`));
});
