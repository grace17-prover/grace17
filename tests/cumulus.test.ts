// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, readdirSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { compileProofModule, createZfgKernel, exportTheorem, exportTheoremForMachine, loadModuleGraph, loadModuleSourceGraph, verifyProofMachine } from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const library = fileURLToPath(new URL("../lib", import.meta.url));
const cumulus = fileURLToPath(new URL("../lib/Grace/Cumulus.g17", import.meta.url));

function g17Files(root: string): string[] {
  return readdirSync(root, { withFileTypes: true }).flatMap(entry => {
    const path = join(root, entry.name);
    return entry.isDirectory() ? g17Files(path) : entry.name.endsWith(".g17") ? [path] : [];
  });
}

test("source headers end with a separating blank line", () => {
  for (const file of [...g17Files(library), ...g17Files(fileURLToPath(new URL("../examples", import.meta.url)))]) {
    const lines = readFileSync(file, "utf8").split(/\r?\n/);
    const authors = lines.indexOf("-- Authors: Grant Passmore");
    assert.notEqual(authors, -1, file);
    assert.equal(lines[authors + 1], "", file);
  }
});

test("the rational density proof uses mathematical operation notation", () => {
  const source = readFileSync(new URL("../lib/Grace/Cumulus/Rat/Density.g17", import.meta.url), "utf8");
  assert.doesNotMatch(source, /\b(?:add|mul)\(/);
  assert.match(source, /n \* a \+ m \* c/);
});

test("Cumulus uses bounded quantifiers for set-sized membership guards", () => {
  const root = join(library, "Grace", "Cumulus");
  const legacy = /[∃∀]\s+([\p{L}_][\p{L}\p{M}\p{N}_]*),\s*\1\s*∈\s*([^∧→\n]+?)\s*[∧→]/gu;
  for (const file of g17Files(root)) {
    const source = readFileSync(file, "utf8");
    for (const match of source.matchAll(legacy)) {
      const bound = match[2]!.trim();
      if (bound === "Ordinal") continue; // A mathematical proper class, not a bounding set.
      const line = source.slice(0, match.index).split("\n").length;
      assert.fail(`${file}:${line}: write this set guard as a bounded quantifier: ${match[0]}`);
    }
  }
});

test("Cumulus source headers stay approachable", () => {
  const cumulusFiles = g17Files(fileURLToPath(new URL("../lib/Grace/Cumulus", import.meta.url)));
  for (const file of cumulusFiles) {
    const source = readFileSync(file, "utf8");
    const imports = source.match(/^import /gm)?.length ?? 0;
    const localOpens = source.match(/^open /gm)?.length ?? 0;
    // Culminating algebra proofs join independently developed subjects. Keep
    // them coherent instead of introducing import-only micro-modules.
    const synthesisLimit = file.endsWith("/Algebra/MatrixAnnihilator.g17") ? 4
      : file.endsWith("/Algebra/Polynomial/Nullstellensatz.g17") ? 8 : 3;
    const limit = file.includes("/Real/Analysis/") ? 8 : synthesisLimit;
    // Subject entrypoints only aggregate modules; the separate root-file test
    // prohibits implementations there. Keep the import budget on proof modules.
    const entrypoint = existsSync(file.slice(0, -4)) && statSync(file.slice(0, -4)).isDirectory();
    if (!entrypoint) {
      assert.ok(imports <= limit, `${file}: expected at most ${limit} imports, found ${imports}`);
    }
    assert.equal(localOpens, 0, `${file}: public scopes should flow through curated export open declarations`);
    assert.doesNotMatch(source,
      /¬\s*(?:[\p{L}_][\p{L}\p{M}\p{N}_]*|\{[^}\n]+\}|[\p{L}_][\p{L}\p{M}\p{N}_]*\([^\n)]*\))\s*=/u,
      `${file}: write negated equality as ≠`);
    assert.doesNotMatch(source, /<->|->/, `${file}: use Unicode → and ↔ in authored Cumulus sources`);
  }

  for (const [relative, expectedImports] of [
    ["Set/Hierarchy.g17", 2],
    ["Cardinal/Sum.g17", 1],
    ["Cardinal/Product.g17", 1],
    ["NumberTheory/Prime.g17", 2],
  ] as const) {
    const source = readFileSync(join(library, "Grace", "Cumulus", relative), "utf8");
    assert.equal(source.match(/^import /gm)?.length ?? 0, expectedImports, relative);
  }
});

test("Cumulus root files are subject entrypoints rather than implementations", () => {
  const root = join(library, "Grace", "Cumulus");
  for (const entry of readdirSync(root, { withFileTypes: true })) {
    if (!entry.isFile() || !entry.name.endsWith(".g17")) continue;
    const source = readFileSync(join(root, entry.name), "utf8");
    assert.match(source, /^module [\p{L}_][\p{L}\p{M}\p{N}_.]*$/mu, entry.name);
    assert.match(source, /^import /m, entry.name);
    assert.doesNotMatch(source, /^(?:def|predicate|class|theorem|lemma|instance|notation|eval|tactic)\b/m,
      `${entry.name}: mathematical content belongs in a subject directory`);
  }
});

test("Cumulus loads over Core and every library theorem replays", () => {
  const kernel = createZfgKernel();
  const loaded = loadModuleGraph(kernel, [cumulus], [library]);
  const libraryTheorems = loaded.filter(item => item.file.startsWith(library)).flatMap(item => item.theorems);
  assert.ok(libraryTheorems.length >= 4826, "retain the validated Cumulus theorem coverage");
  for (const name of libraryTheorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
  for (const name of [
    "Grace.Cumulus.GraphTheory.Counting.SimpleGraph.handshaking",
    "Grace.Cumulus.GraphTheory.Counting.Finite.handshaking",
    "Grace.Cumulus.GraphTheory.Connectivity.GraphConnected.iff_closed_sets",
    "Grace.Cumulus.GraphTheory.Connectivity.GraphConnected.iff_crossing_cuts",
    "Grace.Cumulus.Nat.Parity.Even.not_successor_double",
    "Grace.Cumulus.Nat.Parity.parity.exhaustive",
    "Grace.Cumulus.Nat.Parity.Odd.iff_not_even",
    "Grace.Cumulus.Nat.Parity.Odd.add_odd",
    "Grace.Cumulus.GraphTheory.Multigraph.EulerTrail.three_odd_obstruction",
    "Grace.Cumulus.GraphTheory.Konigsberg.graph",
    "Grace.Cumulus.GraphTheory.Konigsberg.degree_island1",
    "Grace.Cumulus.GraphTheory.Konigsberg.no_euler_trail",
    "Grace.Cumulus.GraphTheory.Konigsberg.no_euler_trail_exists",
    "Grace.Cumulus.GraphTheory.Multigraph.Walk.incidence_balance",
    "Grace.Cumulus.GraphTheory.Multigraph.Walk.closed_even",
    "Grace.Cumulus.GraphTheory.Multigraph.EulerTrail.incidence_reindex",
    "Grace.Cumulus.GraphTheory.Multigraph.EulerTrail.three_noneven_obstruction",
    "Grace.Cumulus.Geometry.Pythagoras.Plane.pythagoras",
    "Grace.Cumulus.Geometry.Isosceles.Euclidean.isosceles",
    "Grace.Cumulus.Geometry.Angle.Euclidean.isosceles.cosines",
    "Grace.Cumulus.Geometry.Angle.Euclidean.law_of_cosines",
    "Grace.Cumulus.Geometry.Distance.Euclidean.distance.triangle",
    "Grace.Cumulus.Geometry.Angle.Euclidean.cosAngle.le_one",
    "Grace.Cumulus.Real.Sqrt.sqrt.square",
    "Grace.Cumulus.Geometry.Circle.Euclidean.thales",
    "Grace.Cumulus.Geometry.Midpoint.Euclidean.apollonius",
    "Grace.Cumulus.Geometry.Midpoint.Euclidean.perpendicular_bisector",
    "Grace.Cumulus.Geometry.Lines.Euclidean.midsegment.parallel",
    "Grace.Cumulus.Geometry.Lines.Euclidean.midsegment.length",
    "Grace.Cumulus.Geometry.Lines.Euclidean.midsegment.equal_vectors",
    "Grace.Cumulus.Geometry.Parallelogram.Euclidean.varignon",
    "Grace.Cumulus.Geometry.Centroid.Euclidean.centroid.concurrency",
    "Grace.Cumulus.Geometry.Centroid.Euclidean.centroid.unique",
    "Grace.Cumulus.Geometry.Centroid.Euclidean.medianRatio.length",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.circumcenter.correct",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.circumcenter.unique",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.euler_line.exists",
    "Grace.Cumulus.Geometry.TriangleCenters.Euclidean.orthocenter.unique",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.orthocenter.exists",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.orthocenter.of_two_altitudes",
    "Grace.Cumulus.Geometry.Circumcenter.Euclidean.orthocenter.eq_constructed",
    "Grace.Cumulus.LinearAlgebra.TwoByTwo.LinearSystem2.correct",
    "Grace.Cumulus.LinearAlgebra.TwoByTwo.LinearSystem2.unique",
    "Grace.Cumulus.Geometry.TriangleCenters.Euclidean.euler_line",
    "Grace.Cumulus.Geometry.TriangleCenters.Euclidean.euler_line.coincident",
    "Grace.Cumulus.Geometry.TriangleCenters.Euclidean.circumcenter.right_triangle",
    "Grace.Cumulus.Geometry.Parallelogram.Euclidean.varignon.parallel",
    "Grace.Cumulus.Geometry.Parallelogram.Euclidean.varignon.constructed",
    "Grace.Cumulus.Geometry.Parallelogram.Euclidean.parallelogram.iff_diagonals",
    "Grace.Cumulus.Geometry.Circle.Euclidean.pythagoras_converse",
    "Grace.Cumulus.Cardinal.Enumeration.HasCardinality.unique",
    "Grace.Cumulus.GraphTheory.CountingInvariant.GraphCount.edgeCount.reindex",
    "Grace.Cumulus.GraphTheory.DijkstraInvariant.Dijkstra.StateInvariant.initial",
    "Grace.Cumulus.GraphTheory.DijkstraCorrectness.Dijkstra.StateInvariant.certifies_minimum",
    "Grace.Cumulus.GraphTheory.DijkstraCorrectness.Dijkstra.StateInvariant.relax_selected",
    "Grace.Cumulus.GraphTheory.DijkstraCorrectness.Dijkstra.StateInvariant.iterate",
    "Grace.Cumulus.GraphTheory.DijkstraCorrectness.Dijkstra.solve.correct",
    "Grace.Cumulus.GraphTheory.DijkstraInvariant.Dijkstra.mark.flag_cases",
    "Grace.Cumulus.GraphTheory.DijkstraInvariant.Dijkstra.mark.open_was_open",
    "Grace.Cumulus.GraphTheory.DijkstraProgress.Dijkstra.solve.exhausts_finite_frontier",
    "Grace.Cumulus.GraphTheory.DijkstraIndex.Dijkstra.minimum.selected_entry",
    "Grace.Cumulus.GraphTheory.DijkstraIndex.Dijkstra.minimum.none_iff_no_open_finite",
    "Grace.Cumulus.GraphTheory.DijkstraStep.Dijkstra.advance.selected_distance",
    "Grace.Cumulus.GraphTheory.DijkstraCut.FrontierTable.certifies_minimum",
    "Grace.Cumulus.GraphTheory.DijkstraProofs.Dijkstra.WitnessedDistance.relax",
    "Grace.Cumulus.GraphTheory.Connectivity.components.equal_or_disjoint",
    "Grace.Cumulus.GraphTheory.Connectivity.component.induced_connected",
    "Grace.Cumulus.Set.Core.Subset.transitive",
    "Grace.Cumulus.Algebra.OrderedField.Core.IsOrderedField.field",
    "Grace.Cumulus.Algebra.OrderedField.Core.IsOrderedField.add_right",
    "Grace.Cumulus.Algebra.OrderedField.Core.IsOrderedField.positive_product",
    "Grace.Cumulus.Real.Core.DedekindCut.comparable",
    "Grace.Cumulus.Real.Core.realLess.connected_on",
    "Grace.Cumulus.Real.Core.realLess.strict_linear_order",
    "Grace.Cumulus.Real.Negation.realLess.add_right",
    "Grace.Cumulus.Real.Negation.realLess.add_right_iff",
    "Grace.Cumulus.Real.Negation.realLess.iff_pos_sub",
    "Grace.Cumulus.Real.Negation.realAdd.strict_mono",
    "Grace.Cumulus.Real.Inverse.realInv.function",
    "Grace.Cumulus.Real.Analysis.Continuity.ContinuousAt.comp",
    "Grace.Cumulus.Real.Analysis.Continuity.ContinuousAt.add",
    "Grace.Cumulus.Real.Analysis.Continuity.ContinuousAt.mul",
    "Grace.Cumulus.Real.Analysis.Continuity.ContinuousAt.inv",
    "Grace.Cumulus.Real.Analysis.Continuity.ContinuousAt.div",
    "Grace.Cumulus.Real.Analysis.Sequences.openBall.order_characterization",
    "Grace.Cumulus.Real.Analysis.Sequences.ConvergesTo.eventually_bounded",
    "Grace.Cumulus.Real.Analysis.Sequences.ConvergesTo.le_of_le_terms",
    "Grace.Cumulus.Real.Analysis.Sequences.ConvergesTo.squeeze",
    "Grace.Cumulus.Real.Inverse.reals.multiplicative_inverse",
    "Grace.Cumulus.Real.Inverse.reals.field",
    "Grace.Cumulus.Real.Inverse.reals.ordered_field",
    "Grace.Cumulus.Real.Inverse.realDiv.function",
    "Grace.Cumulus.Real.Inverse.realDiv.eq_mul_inv",
    "Grace.Cumulus.Real.Squares.realInvValue.antitone_positive",
    "Grace.Cumulus.Real.AbsoluteValue.abs.inv",
    "Grace.Cumulus.Real.Metric.dist.inv_inv",
    "Grace.Cumulus.Real.Analysis.Sequences.ConvergesTo.inv",
    "Grace.Cumulus.Real.Analysis.Sequences.ConvergesTo.div",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.affinePoint.dyadic_endpoint",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.affinePoints.dyadic_fine",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FineTaggedPartitionsExist.positive_interval",
    "Grace.Cumulus.Real.Analysis.Integration.IntegralOrderBound.HasRiemannIntegral.unique_on_interval",
    "Grace.Cumulus.Real.Analysis.Integration.IntegralOrderBound.functionIncrements.telescoping",
    "Grace.Cumulus.Real.Analysis.Integration.IntegralOrderBound.TaggedPartition.riemann_sum_of_cell_increments",
    "Grace.Cumulus.Real.Analysis.Integration.IntegralOrderBound.HasRiemannIntegral.eq_endpoint_of_mean_value",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.realFunctionImage.sequentially_compact",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.SequentiallyCompact.contains_supremum",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.ContinuousOn.closed_interval_maximum_of_upper_bound",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.SequentiallyCompact.bounded_above",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.ContinuousOn.closed_interval_maximum",
    "Grace.Cumulus.Real.Analysis.ExtremeValue.ContinuousOn.closed_interval_minimum",
    "Grace.Cumulus.Real.Analysis.MeanValueIntegration.HasDerivativeAt.zero_at_interval_max",
    "Grace.Cumulus.Real.Analysis.MeanValueIntegration.Rolle.theorem",
    "Grace.Cumulus.Real.Analysis.Continuity.TendsToAt.unique",
    "Grace.Cumulus.Real.Analysis.Differentiation.HasDerivativeAt.unique",
    "Grace.Cumulus.Real.Analysis.Intervals.ContinuousOn.mul",
    "Grace.Cumulus.Real.Analysis.MeanValueIntegration.MeanValue.theorem",
    "Grace.Cumulus.Real.Analysis.MeanValueIntegration.CellMeanValueProperty.of_derivative",
    "Grace.Cumulus.Real.Analysis.MeanValueIntegration.HasRiemannIntegral.eq_endpoint_of_derivative",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FinePartition.cell_points_distance",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.ContinuousOn.fine_cell_oscillation",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.FTC.continuous_derivative",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.RiemannIntegrable.continuous_derivative",
    "Grace.Cumulus.Real.Analysis.Integration.IndefiniteIntegral.ContinuousOn.partition_cell",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.CellMeanValueWitnesses.of_local_derivative",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.HasRiemannIntegral.eq_endpoint_of_local_derivative",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.CauchySequence.converges_in_interval",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.riemannSum.continuous_bounds",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.dyadicRiemannSums.fine_grid",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.dyadicRiemannSums.bounded",
    "Grace.Cumulus.Real.Analysis.Integration.RiemannSums.dyadicRiemannSums.converges_of_cauchy",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FineCellOscillation.subdivision_bounds",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FineCellOscillation.cellwise_subdivision_bounds",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FineCellOscillation.compare_shared_subdivision",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.SharedSubdivisionTotal.one_cell",
    "Grace.Cumulus.Real.Analysis.Integration.CommonRefinementComparison.FineCellOscillation.compare_one_cell",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.riemannSum.split_at",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.split_tagged_sum",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.IntervalPartition.insert_first_cell",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.insert_first_cell_tagged",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.indexedInsertedPoints.inserted",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.prepend",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.insert_at_tagged",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.insert_indexed_split",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.SharedSubdivisionTotal.first_cell_inserted",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.FinePartition.shared_subdivision",
    "Grace.Cumulus.Real.Analysis.Integration.ContinuousIntegral.ContinuousOn.integrable_interval",
    "Grace.Cumulus.Real.Analysis.Integration.IndefiniteIntegral.HasRiemannIntegral.add_interior",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.FTC.derivative_of_integral",
    "Grace.Cumulus.Real.Analysis.Integration.FTCFirst.riemannIntegral.of_continuous_derivative",
    "Grace.Cumulus.Real.FiniteSum.realPartialSum.add",
    "Grace.Cumulus.Real.Polynomial.polynomialEval.linear",
    "Grace.Cumulus.Real.Order.realLe.characterization",
    "Grace.Cumulus.Real.Order.realLe.of_subset",
    "Grace.Cumulus.Real.Squares.realMulValue.square_nonnegative",
    "Grace.Cumulus.Real.Squares.realMulValue.square_positive",
    "Grace.Cumulus.Real.Squares.realMulValue.square_eq_zero_iff",
    "Grace.Cumulus.Real.Squares.realAddValue.sum_squares_nonnegative",
    "Grace.Cumulus.Rat.OrderedOperations.rationalLess.mul_positive",
    "Grace.Cumulus.Rat.OrderedOperations.rationalLess.mul_left",
    "Grace.Cumulus.Real.Multiplication.realPosMulCut.cut",
    "Grace.Cumulus.Real.Multiplication.realPosMulCut.real",
    "Grace.Cumulus.Real.Multiplication.realPositivePart.real",
    "Grace.Cumulus.Real.Multiplication.realNegativePart.real",
    "Grace.Cumulus.Real.Multiplication.realMulCut.real",
    "Grace.Cumulus.Set.Hierarchy.rank.membership",
    "Grace.Cumulus.Set.Hierarchy.CumulativeUniverse.eq_Universe",
    "Grace.Cumulus.Set.Relation.product.monotone",
    "Grace.Cumulus.Set.Foundation.membershipOn.relation",
    "Grace.Cumulus.Set.Order.Ordinal.well_order",
    "Grace.Cumulus.Set.Order.Ordinal.member_proper_initial_segment",
    "Grace.Cumulus.Cardinal.Hartogs.activeWellOrderRelation.well_founded",
    "Grace.Cumulus.Cardinal.Hartogs.activeWellOrderRelation.transitive",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCollapse.membership",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCollapse.ordinal",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCollapse.injective",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCollapseGraph.function",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCollapseGraph.order_isomorphism",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderType.ordinal",
    "Grace.Cumulus.Cardinal.Hartogs.wellOrderCodes.nonempty",
    "Grace.Cumulus.Set.Function.Bijective.injective",
    "Grace.Cumulus.Set.Function.identity.function",
    "Grace.Cumulus.Set.Function.identity.bijective",
    "Grace.Cumulus.Set.Function.converse.bijective",
    "Grace.Cumulus.Set.Function.compose.function",
    "Grace.Cumulus.Set.Function.compose.bijective",
    "Grace.Cumulus.Set.Function.adjoinMap.bijective",
    "Grace.Cumulus.Set.Function.compose.identity_left",
    "Grace.Cumulus.Set.Function.compose.identity_right",
    "Grace.Cumulus.Relation.Core.Equivalence.transitive",
    "Grace.Cumulus.Relation.Quotient.equivalenceClass.eq",
    "Grace.Cumulus.Relation.Quotient.equivalenceClass.related_of_eq",
    "Grace.Cumulus.Relation.Quotient.equivalenceClass.members_related",
    "Grace.Cumulus.Relation.Quotient.quotient.members_related",
    "Grace.Cumulus.Relation.Quotient.quotient.member_nonempty",
    "Grace.Cumulus.Int.Defs.integerPairs.pair",
    "Grace.Cumulus.Int.Defs.integerEquivalent.reflexive_pair",
    "Grace.Cumulus.Int.Defs.integerEquivalent.cross_symmetric",
    "Grace.Cumulus.Int.Defs.integerEquivalent.relation",
    "Grace.Cumulus.Int.Defs.integerEquivalent.equivalence",
    "Grace.Cumulus.Int.Core.integerClass.eq",
    "Grace.Cumulus.Int.Operations.integerClassSum.well_defined",
    "Grace.Cumulus.Int.Operations.integerClassNeg.well_defined",
    "Grace.Cumulus.Rat.Defs.rationalEquivalent.relation",
    "Grace.Cumulus.Rat.Defs.rationalEquivalent.symmetric",
    "Grace.Cumulus.Rat.Defs.Rational.representative",
    "Grace.Cumulus.Rat.Defs.Rational.members_related",
    "Grace.Cumulus.Nat.Order.mul.left_cancel_positive",
    "Grace.Cumulus.Rat.Order.rationalLess.bounded",
    "Grace.Cumulus.Rat.Order.rationalLess.representatives",
    "Grace.Cumulus.Rat.Order.rationalRepresentativeLess.not_equivalent",
    "Grace.Cumulus.Rat.Order.rationalLess.irreflexive_on",
    "Grace.Cumulus.Rat.Operations.rationalClassSum.well_defined",
    "Grace.Cumulus.Rat.Operations.rationalClassSum.associative",
    "Grace.Cumulus.Rat.Operations.rationalClassMul.well_defined",
    "Grace.Cumulus.Rat.Operations.rationalClassMul.associative",
    "Grace.Cumulus.Rat.Operations.rationalClassMul.distributive_left",
    "Grace.Cumulus.Rat.Operations.rationalAdd.function",
    "Grace.Cumulus.Rat.Operations.rationalMul.function",
    "Grace.Cumulus.Rat.Operations.rationalAddValue.rational",
    "Grace.Cumulus.Rat.Operations.rationalMulValue.rational",
    "Grace.Cumulus.Rat.Operations.rationalAddValue.classes",
    "Grace.Cumulus.Rat.Operations.rationalMulValue.classes",
    "Grace.Cumulus.Real.Core.DedekindCut.downward",
    "Grace.Cumulus.Real.Core.Real.extensionality",
    "Grace.Cumulus.Real.Core.RealLess.transitive",
    "Grace.Cumulus.Real.Core.realLess.strict_order",
    "Grace.Cumulus.Real.Core.rationalCut.subset_rationals",
    "Grace.Cumulus.Real.Order.RealLe.antisymmetric",
    "Grace.Cumulus.Real.Order.realSup.cut",
    "Grace.Cumulus.Real.Order.realSup.least_upper_bound",
    "Grace.Cumulus.Real.Order.Real.least_upper_bound_property",
    "Grace.Cumulus.Cardinal.Finite.Equipotent.reflexive",
    "Grace.Cumulus.Cardinal.Finite.Equipotent.symmetric",
    "Grace.Cumulus.Cardinal.Finite.Equipotent.transitive",
    "Grace.Cumulus.Cardinal.Finite.Finite.natural",
    "Grace.Cumulus.Cardinal.Finite.Finite.empty",
    "Grace.Cumulus.Cardinal.Finite.singletonEquiv.bijective",
    "Grace.Cumulus.Cardinal.Finite.Finite.singleton",
    "Grace.Cumulus.Cardinal.Sum.disjointSum.left",
    "Grace.Cumulus.Cardinal.Sum.disjointSum.membership",
    "Grace.Cumulus.Cardinal.Sum.tags.disjoint",
    "Grace.Cumulus.Cardinal.Sum.sumMap.function",
    "Grace.Cumulus.Cardinal.Sum.sumMap.bijective",
    "Grace.Cumulus.Cardinal.Sum.Equipotent.disjointSum",
    "Grace.Cumulus.Cardinal.Sum.natSumEquiv.bijective",
    "Grace.Cumulus.Cardinal.Sum.HasCardinality.disjointSum",
    "Grace.Cumulus.Cardinal.Sum.Finite.disjointSum",
    "Grace.Cumulus.Cardinal.Product.productMap.bijective",
    "Grace.Cumulus.Cardinal.Product.Equipotent.product",
    "Grace.Cumulus.Cardinal.Product.productStepMap.bijective",
    "Grace.Cumulus.Cardinal.Product.natProductEquiv.bijective",
    "Grace.Cumulus.Cardinal.Product.Equipotent.nat_product",
    "Grace.Cumulus.Cardinal.Product.HasCardinality.product",
    "Grace.Cumulus.Cardinal.Product.Finite.product",
    "Grace.Cumulus.Set.Order.Least.unique",
    "Grace.Cumulus.Set.Order.Chain.union",
    "Grace.Cumulus.Set.Order.ZornCondition.nonempty",
    "Grace.Cumulus.Nat.Core.add.left_cancel",
    "Grace.Cumulus.Nat.Pow.pow.add",
    "Grace.Cumulus.Nat.Foundation.membership.successor",
    "Grace.Cumulus.Nat.Foundation.membership.two_in_five",
    "Grace.Cumulus.Nat.Foundation.membership.one",
    "Grace.Cumulus.Nat.Foundation.natural.zero_one_or_above_one",
    "Grace.Cumulus.Nat.Order.Less.trichotomy",
    "Grace.Cumulus.Nat.Order.membership.of_Less",
    "Grace.Cumulus.Nat.Core.factorial.closed",
    "Grace.Cumulus.Nat.Mod.equalNat.reflexive",
    "Grace.Cumulus.Nat.Mod.mod.zero_right",
    "Grace.Cumulus.Nat.Mod.mod.one",
    "Grace.Cumulus.NumberTheory.Divisibility.divides.transitive",
    "Grace.Cumulus.NumberTheory.Divisibility.factorial.successor_divides",
    "Grace.Cumulus.NumberTheory.Divisibility.factorial.divisible_through",
    "Grace.Cumulus.NumberTheory.Divisibility.divides.consecutive_one",
    "Grace.Cumulus.NumberTheory.Prime.Prime.natural",
    "Grace.Cumulus.NumberTheory.Prime.primes.membership",
    "Grace.Cumulus.NumberTheory.Prime.primes.contains",
    "Grace.Cumulus.NumberTheory.Prime.natural.exists_prime_divisor",
    "Grace.Cumulus.NumberTheory.Prime.factorial.successor_greater_than_one",
    "Grace.Cumulus.NumberTheory.Prime.primes.unbounded",
    "Grace.Cumulus.NumberTheory.Prime.Euclid.larger_prime",
    "Grace.Cumulus.NumberTheory.Prime.factorial_successor.exists_prime_divisor",
    "Grace.Cumulus.NumberTheory.Prime.prime_divisor.factorial_successor_greater",
    "Grace.Cumulus.NumberTheory.Infinitude.primes.infinite",
    "Grace.Cumulus.NumberTheory.Infinitude.primes.order_unbounded",
    "Grace.Cumulus.NumberTheory.Factorization.Prime.divides_mul",
    "Grace.Cumulus.NumberTheory.Factorization.primeFactorization.exists",
    "Grace.Cumulus.NumberTheory.Factorization.primeFactorization.unique",
    "Grace.Cumulus.NumberTheory.Factorization.primeFactorization.fundamental_theorem",
    "Grace.Cumulus.NumberTheory.RootTwo.rootTwo.irrational",
    "Grace.Cumulus.Nat.Induction.natural.induction",
    "Grace.Cumulus.Real.MeanInequality.sqrt.le_mean",
    "Grace.Cumulus.Real.RootTwo.sqrtTwo.ne_quotient",
    "Grace.Cumulus.Real.Rationals.sqrtTwo.not_rational",
    "Grace.Cumulus.Real.RationalEmbedding.rationalCut.add",
    "Grace.Cumulus.Real.TriangularSum.realPartialSum.triangular_reciprocals",
    "Grace.Cumulus.Rat.Countable.rationals.countable",
    "Grace.Cumulus.Real.Analysis.IntermediateValue.closedInterval.intermediate_value",
    "Grace.Cumulus.Cardinal.PowersetCount.powerset.cardinality",
    "Grace.Cumulus.Cardinal.CountableClosure.Countable.of_surjection",
    "Grace.Cumulus.NumberTheory.DigitSum.digitsValue.three_divides_iff",
    "Grace.Cumulus.Cardinal.Finite.Finite.naturals_bounded",
    "Grace.Cumulus.Cardinal.Finite.infinite.of_unbounded_naturals",
    "Grace.Cumulus.Cardinal.Finite.omega.order_unbounded",
    "Grace.Cumulus.Cardinal.Finite.omega.infinite",
    "Grace.Cumulus.Algebra.Group.Core.IsInverse.unique",
    "Grace.Cumulus.Algebra.Ring.Core.IsIntegralDomain.comm_ring",
    "Grace.Cumulus.Algebra.Field.Core.IsFieldWithInverse.division_ring",
    "Grace.Cumulus.Real.ArithmeticSeries.arithmeticSeries.quotient",
    "Grace.Cumulus.Real.ArithmeticSeries.arithmeticSeries.odd_sum",
    "Grace.Cumulus.Real.Natural.realNat.mul",
  ]) assert.equal(kernel.theorems.has(name), true, name);
  assert.deepEqual(loaded.filter(item => item.file.startsWith(library)).flatMap(item => item.evaluations.map(value => value.value)), [
    "126", "3833759992447475122176", "true", "2", "3", "3", "2",
    "true", "[[fraction(1, 0, 1), fraction(1, 0, 1), fraction(3, 0, 1)], [fraction(1, 1, 2), fraction(2, 0, 2), fraction(3, 1, 2)]]",
    "[[fraction(3, 1, 2), fraction(2, 2, 2), fraction(7, 3, 2)], [fraction(1, 1, 2), fraction(2, 0, 2), fraction(3, 1, 2)]]",
    "[some(0), some(7), some(3), some(9), some(5), none]",
  ]);
  const machine = compileProofModule(libraryTheorems.map(name => exportTheoremForMachine(kernel, name)));
  assert.equal(verifyProofMachine(kernel, machine).stats.instructions, machine.code.length);
  const central = exportTheorem(kernel, "Grace.Cumulus.Cardinal.Product.natProductEquiv.bijective");
  assert.deepEqual(central.tactics?.narrative.filter(entry => entry.kind === "heading").map(entry => entry.text), [
    "Decompose the successor rectangle.",
    "Transport the old block and the new row.",
    "Pack the two finite blocks into multiplication.",
  ]);
});

test("Cumulus Main provides a one-import set and arithmetic environment", () => {
  const kernel = createZfgKernel();
  const source = `module User.MainDemo
namespace User.MainDemo
import Grace.Cumulus.Main

lemma arithmetic_and_sets
  shows {1, 1, 2} = {1, 2} and 2 + 3 = 5
proof
  constructor
  . ext x
    simp
  . settle with add

end User.MainDemo
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "MainDemo.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, ["User.MainDemo.arithmetic_and_sets"]);
  const modules = new Set(loaded.map(item => item.module));
  assert.equal(modules.has("Grace.Cumulus.Main"), true);
  assert.equal(modules.has("Grace.Cumulus.NumberTheory"), false);
  assert.equal(modules.has("Grace.Cumulus.Algebra"), false);
});

test("typed arithmetic notation selects natural and rational operations", () => {
  const kernel = createZfgKernel();
  const source = `module User.TypedArithmetic
namespace User.TypedArithmetic
import Grace.Cumulus.Rat

lemma natural.notation (x y : Nat)
  shows x + y = add(x, y)
proof
  rfl

lemma rational.notation (x y : Rational)
  shows x + y = rationalAddValue(x, y)
proof
  exact rationalAddValue.notation at x, y

lemma rational.closed (x y : Rational)
  shows Rational(x + y)
proof
  exact rationalAddValue.rational at x, y with assumption, assumption

lemma rational.one_right (x : Rational)
  shows x * 1 = x
proof
  exact rationalMulValue.one_right at x with assumption

lemma rational.one_left (x : Rational)
  shows 1 * x = x
proof
  exact rationalMulValue.one_left at x with assumption

end User.TypedArithmetic
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "TypedArithmetic.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.TypedArithmetic.natural.notation",
    "User.TypedArithmetic.rational.notation",
    "User.TypedArithmetic.rational.closed",
    "User.TypedArithmetic.rational.one_right",
    "User.TypedArithmetic.rational.one_left",
  ]);
});

test("real unit notation propagates its carrier from either operand", () => {
  const kernel = createZfgKernel();
  const source = `module User.RealUnitNotation
namespace User.RealUnitNotation
import Grace.Cumulus.Real.Multiplication

lemma real.one_right (A : Real)
  requires nonnegative : realZero ⊆ A
  shows A * 1 = A
proof
  exact realMulValue.one_right_of_nonnegative at A with assumption, nonnegative

lemma real.one_left (A : Real)
  requires nonnegative : realZero ⊆ A
  shows 1 * A = A
proof
  exact realMulValue.one_left_of_nonnegative at A with assumption, nonnegative

end User.RealUnitNotation
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "RealUnitNotation.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.RealUnitNotation.real.one_right",
    "User.RealUnitNotation.real.one_left",
  ]);
});

test("real function applications inherit their codomain for notation", () => {
  const kernel = createZfgKernel();
  const source = `module User.RealFunctionValues
namespace User.RealFunctionValues
import Grace.Cumulus.Real.Analysis.Continuity

lemma real_function.zero_right (f : Set) (A : Real)
  requires function : FunctionBetween(f, ℝ, ℝ)
  shows apply(f, A) + 0 = apply(f, A)
proof
  have valueReal : Real(apply(f, A))
    typecheck
  exact realAddValue.zero_right at apply(f, A) with valueReal

end User.RealFunctionValues
`;
  const loaded = loadModuleSourceGraph(kernel,
    [{ file: "RealFunctionValues.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems,
    ["User.RealFunctionValues.real_function.zero_right"]);
});

test("real linarith replays checked order and addition rules", () => {
  const kernel = createZfgKernel();
  const source = `module User.RealLinearOrder
namespace User.RealLinearOrder
import Grace.Cumulus.Real.Analysis.HeineCantor

lemma strict_sum (x y u v : Real)
  requires first : x < y
  requires second : u < v
  shows x + u < y + v
proof
  linarith

lemma mixed_transitivity (x y z : Real)
  requires first : x ≤ y
  requires second : y < z
  shows x < z
proof
  linarith

end User.RealLinearOrder
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "RealLinearOrder.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.RealLinearOrder.strict_sum",
    "User.RealLinearOrder.mixed_transitivity",
  ]);
});

test("real linarith composes subtraction and addition at arbitrary depth", () => {
  const kernel = createZfgKernel();
  const source = `module User.RealAffineOrder
namespace User.RealAffineOrder
import Grace.Cumulus.Real.Ring

lemma interval (a b c : Real)
  requires lower : a ≤ b
  requires upper : b ≤ c
  shows (0:R) ≤ b - a ∧ b - a ≤ c - a
proof
  constructor
  . linarith
  . linarith

lemma opposite_sides (a b c d : Real)
  requires left : a ≤ c
  requires right : d ≤ b
  shows a - b ≤ c - d
proof
  linarith

lemma nested (a b c d e f : Real)
  requires left : a ≤ c
  requires right : d ≤ b
  requires extra : e ≤ f
  shows (a - b) + e ≤ (c - d) + f
proof
  linarith

lemma strict_difference (a b c : Real)
  requires bound : a < b
  shows (0:R) < b - a ∧ a - c < b - c
proof
  constructor
  . linarith
  . linarith

lemma negate_order (a b : Real)
  requires bound : a ≤ b
  shows -b ≤ -a
proof
  linarith

end User.RealAffineOrder
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "RealAffineOrder.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.RealAffineOrder.interval", "User.RealAffineOrder.opposite_sides",
    "User.RealAffineOrder.nested", "User.RealAffineOrder.strict_difference",
    "User.RealAffineOrder.negate_order",
  ]);
});

test("linarith uses checked ordered-ring instances for abstract affine proofs", () => {
  const kernel = createZfgKernel();
  const source = `module User.AbstractLinearOrder
namespace User.AbstractLinearOrder
import Grace.Cumulus.Algebra.OrderedAdditive

lemma translated (A add zero neg mul one le x y z : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  requires xy : relates(le, x, y)
  shows relates(le, call2(add, x, z), call2(add, y, z))
proof
  linarith

lemma difference (A add zero neg mul one le x y : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires xy : relates(le, x, y)
  shows relates(le, zero, call2(add, y, neg(x)))
proof
  linarith

lemma subtract_bounds (A add zero neg mul one le x y z w : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  requires hw : w ∈ A
  requires xy : relates(le, x, y)
  requires zw : relates(le, z, w)
  shows relates(le, call2(add, x, neg(w)),
    call2(add, y, neg(z)))
proof
  linarith

end User.AbstractLinearOrder
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "AbstractLinearOrder.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.AbstractLinearOrder.translated", "User.AbstractLinearOrder.difference",
    "User.AbstractLinearOrder.subtract_bounds",
  ]);
});

test("ordered-ring linarith combines many bounds with reassociation and cancellation", () => {
  for (const count of [8, 20]) {
  const kernel = createZfgKernel();
  const xs = Array.from({ length: count }, (_, index) => `x${index}`);
  const ys = Array.from({ length: count }, (_, index) => `y${index}`);
  const add = (items: readonly string[]): string => items.length === 1 ? items[0]! :
    `call2(add, ${items[0]}, ${add(items.slice(1))})`;
  const source = `module User.AbstractAffine${count}
namespace User.AbstractAffine${count}
import Grace.Cumulus.Algebra.OrderedAdditive

theorem rearranged (A add zero neg mul one le ${[...xs, ...ys].join(" ")} : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
${[...xs, ...ys].map(name => `  requires h${name} : ${name} ∈ A`).join("\n")}
${xs.map((name, index) => `  requires bound${index} : relates(le, ${name}, ${ys[index]})`).join("\n")}
  shows relates(le, ${add(xs)}, ${add([...ys].reverse())})
proof
  linarith

theorem cancelled (A add zero neg mul one le ${[...xs, ...ys].join(" ")} : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
${[...xs, ...ys].map(name => `  requires h${name} : ${name} ∈ A`).join("\n")}
${xs.map((name, index) => `  requires bound${index} : relates(le, ${name}, ${ys[index]})`).join("\n")}
  shows relates(le, ${add([...xs, "neg(y0)"])}, ${add(ys.slice(1).reverse())})
proof
  linarith
end User.AbstractAffine${count}
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: `AbstractAffine${count}.g17`, source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    `User.AbstractAffine${count}.rearranged`, `User.AbstractAffine${count}.cancelled`,
  ]);
  }
});

test("ring uses checked CommRing and OrderedRing instances for signed polynomials", () => {
  const abstract = `module User.GenericRing
namespace User.GenericRing
import Grace.Cumulus.Algebra.OrderedAdditive

theorem cancel (A add zero neg mul one le x y z : Set)
  requires structure : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  shows call2(add, call2(add, x, neg(y)), call2(add, z, y)) = call2(add, x, z)
proof
  ring

theorem distribute (A add zero neg mul one x y z : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  shows call2(mul, call2(add, x, y), call2(add, z, one)) =
    call2(add, call2(add, call2(mul, y, z), x), call2(add, call2(mul, z, x), y))
proof
  ring

theorem zero_product (A add zero neg mul one x y : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  shows call2(mul, call2(add, x, neg(x)), y) = zero
proof
  ring

theorem normalize_goal (A add zero neg mul one x y : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires h : zero = y
  shows call2(add, x, neg(x)) = y
proof
  ring_nf
  exact h

theorem normalize_fact (A add zero neg mul one x y : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires h : call2(add, x, neg(x)) = y
  shows zero = y
proof
  ring_nf at h
  exact h

theorem normalize_with_ring_at (A add zero neg mul one x y : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires h : call2(add, x, neg(x)) = y
  shows zero = y
proof
  ring at h
  exact h

theorem normalize_predicate (A add zero neg mul one le x y : Set)
  requires structure : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires h : relates(le, call2(add, x, neg(x)), y)
  shows relates(le, zero, y)
proof
  ring_nf at h
  exact h

theorem normalize_predicate_goal (A add zero neg mul one le x y : Set)
  requires structure : OrderedRing(A, add, zero, neg, mul, one, le)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires h : relates(le, zero, y)
  shows relates(le, call2(add, x, neg(x)), y)
proof
  ring_nf
  exact h

end User.GenericRing
`;
  const kernel = createZfgKernel();
  const loaded = loadModuleSourceGraph(kernel, [{ file: "GenericRing.g17", source: abstract }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.GenericRing.cancel", "User.GenericRing.distribute", "User.GenericRing.zero_product",
    "User.GenericRing.normalize_goal", "User.GenericRing.normalize_fact",
    "User.GenericRing.normalize_with_ring_at", "User.GenericRing.normalize_predicate",
    "User.GenericRing.normalize_predicate_goal",
  ]);
  const real = `module User.RealRingCertificate
namespace User.RealRingCertificate
import Grace.Cumulus.Real.Ring

theorem differences (A B C : Real)
  shows realAddValue(B - A, C - B) = C - A
proof
  ring

end User.RealRingCertificate
`;
  const realLoaded = loadModuleSourceGraph(createZfgKernel(),
    [{ file: "RealRingCertificate.g17", source: real }], [library]);
  assert.deepEqual(realLoaded.at(-1)?.theorems, ["User.RealRingCertificate.differences"]);
});

test("defgraph produces replayable graph, function, and value laws", () => {
  const kernel = createZfgKernel();
  const source = `module User.TypedGraph
namespace User.TypedGraph
import Grace.Cumulus.Real.Analysis

defgraph dyadicGraph (n : Nat) : Real := dyadicRadius(n)
defgraph identityGraph (x : Real) : Real := x
defgraph successorGraph (k : Nat) : Nat := succ(k)

lemma dyadic_value (n : Nat)
  shows dyadicGraph[n] = dyadicRadius(n)
proof
  exact dyadicGraph.value at n with assumption

end User.TypedGraph
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "TypedGraph.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.TypedGraph.dyadicGraph.closed", "User.TypedGraph.dyadicGraph.relates",
    "User.TypedGraph.dyadicGraph.function", "User.TypedGraph.dyadicGraph.value",
    "User.TypedGraph.identityGraph.closed", "User.TypedGraph.identityGraph.relates",
    "User.TypedGraph.identityGraph.function", "User.TypedGraph.identityGraph.value",
    "User.TypedGraph.successorGraph.closed", "User.TypedGraph.successorGraph.relates",
    "User.TypedGraph.successorGraph.function", "User.TypedGraph.successorGraph.value",
    "User.TypedGraph.dyadic_value",
  ]);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
});

test("defgraph rejects an unproved codomain claim", () => {
  const kernel = createZfgKernel();
  const source = `module User.BadTypedGraph
namespace User.BadTypedGraph
import Grace.Cumulus.Real.Defs
defgraph badGraph (n : Nat) : Real := n

end User.BadTypedGraph
`;
  assert.throws(() => loadModuleSourceGraph(kernel,
    [{ file: "BadTypedGraph.g17", source }], [library]),
  /defgraph badGraph needs a checked Real value/);
});

test("bounded defgraph keeps codomain evidence explicit and proves application", () => {
  const kernel = createZfgKernel();
  const source = `module User.InclusionGraph
namespace User.InclusionGraph
import Grace.Cumulus.Set.Inclusion

defgraph restrictedInclusion (A B : Set) (x ∈ A) : B := x
requires subset : A ⊆ B
proof
  unfold Subset at subset
  exact subset with x, member

defgraph constantGraph (A B y : Set) (x ∈ A) : B := y
requires valueInB : y ∈ B
proof
  exact valueInB

theorem restrictedInclusion_use (A B x : Set)
  requires subset : A ⊆ B
  requires member : x ∈ A
  shows restrictedInclusion(A, B)[x] = x
proof
  exact restrictedInclusion.value at A, B, x with subset, member

theorem constantGraph_use (A B x y : Set)
  requires member : x ∈ A
  requires valueInB : y ∈ B
  shows constantGraph(A, B, y)[x] = y
proof
  exact constantGraph.value at A, B, y, x with valueInB, member

end User.InclusionGraph
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "InclusionGraph.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.InclusionGraph.restrictedInclusion.closed",
    "User.InclusionGraph.restrictedInclusion.relates",
    "User.InclusionGraph.restrictedInclusion.function",
    "User.InclusionGraph.restrictedInclusion.value",
    "User.InclusionGraph.constantGraph.closed",
    "User.InclusionGraph.constantGraph.relates",
    "User.InclusionGraph.constantGraph.function",
    "User.InclusionGraph.constantGraph.value",
    "User.InclusionGraph.restrictedInclusion_use",
    "User.InclusionGraph.constantGraph_use",
  ]);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
});

test("bounded defgraph refuses an invalid codomain certificate", () => {
  const kernel = createZfgKernel();
  const source = `module User.BadInclusionGraph
namespace User.BadInclusionGraph
import Grace.Cumulus.Set.Function
defgraph impossible (A : Set) (x ∈ A) : empty := x
proof
  exact member

end User.BadInclusionGraph
`;
  assert.throws(() => loadModuleSourceGraph(kernel,
    [{ file: "BadInclusionGraph.g17", source }], [library]),
  /defgraph impossible needs a checked codomain proof/);
});

test("bounded defgraph accepts typed parameters, Nat indices, and multiline requirements", () => {
  const kernel = createZfgKernel();
  const source = `module User.TypedBoundedGraph
namespace User.TypedBoundedGraph
import Grace.Cumulus.Real.Core

defgraph constantReal (E : Real) (n ∈ ℕ) : ℝ := E
requires evidence : E ∈ ℝ ∧
  E ∈ ℝ
proof
  rcases evidence with ⟨realE, again⟩
  exact realE

theorem constantReal_use (E : Real, n : Nat)
  requires evidence : E ∈ ℝ ∧ E ∈ ℝ
  shows constantReal(E)[n] = E
proof
  exact constantReal.value at E, n with evidence

end User.TypedBoundedGraph
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "TypedBoundedGraph.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.TypedBoundedGraph.constantReal.closed",
    "User.TypedBoundedGraph.constantReal.relates",
    "User.TypedBoundedGraph.constantReal.function",
    "User.TypedBoundedGraph.constantReal.value",
    "User.TypedBoundedGraph.constantReal_use",
  ]);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
});

test("bounded defgraph accepts a parameterized recursive Nat value", () => {
  const kernel = createZfgKernel();
  const source = `module User.RecursiveGraph
namespace User.RecursiveGraph
import Grace.Cumulus.Real.Core

def recursivePoint (A : Real, n : Nat) → Set
  | A, zero => A
  | A, succ(k) => A

theorem recursivePoint.real (A : Real, n : Nat)
  shows Real(recursivePoint(A, n))
proof
  induction n
  | zero =>
    rw recursivePoint
    assumption
  | succ(k) using ih =>
    rw recursivePoint
    assumption

defgraph recursivePoints (A : Real) (n ∈ ℕ) : ℝ := recursivePoint(A, n)
proof
  have realPoint := recursivePoint.real at A, n with assumption, assumption
  unfold Real at realPoint
  exact realPoint

theorem recursivePoints_use (A : Real, n : Nat)
  shows recursivePoints(A)[n] = recursivePoint(A, n)
proof
  exact recursivePoints.value at A, n with assumption, assumption

end User.RecursiveGraph
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "RecursiveGraph.g17", source }], [library]);
  assert.equal(loaded.at(-1)?.theorems.includes("User.RecursiveGraph.recursivePoints.value"), true);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
});

test("defchoose checks existence and selection beneath a bounded existential", () => {
  const kernel = createZfgKernel();
  const source = `module User.BoundedChoice
namespace User.BoundedChoice
import Grace.Cumulus.Real.Core
import Grace.Cumulus.Set.Choice
defchoose chosenReal (E : Real) (X ∈ ℝ) :=
  ∃ Y ∈ ℝ, X = Y
requires realE : E ∈ ℝ
proof
  witness E
  constructor
  . exact realE
  . witness E
    refine ⟨realE, rfl⟩

theorem chosenReal_use (E : Real)
  requires realE : E ∈ ℝ
  shows ∃ Y ∈ ℝ, chosenReal(E) = Y
proof
  have selected := chosenReal.selected at E with realE
  rcases selected with ⟨_, property⟩
  exact property

end User.BoundedChoice
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "BoundedChoice.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.BoundedChoice.chosenReal.exists",
    "User.BoundedChoice.chosenReal.selected",
    "User.BoundedChoice.chosenReal_use",
  ]);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
  const invalid = `module User.InvalidChoice
namespace User.InvalidChoice
import Grace.Cumulus.Set.Choice
defchoose impossible (A : Set) (x ∈ A) := x ∈ empty
proof
  witness empty
  refine ⟨rfl, rfl⟩

end User.InvalidChoice
`;
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(),
    [{ file: "InvalidChoice.g17", source: invalid }], [library]),
  /defchoose impossible needs a checked existence proof/);
});

test("expression carrier annotations select real numerals and relations without admitting typing facts", () => {
  const kernel = createZfgKernel();
  const source = `module User.AnnotatedReal
namespace User.AnnotatedReal
import Grace.Cumulus.Real.Analysis.Sequences
theorem annotated_zero
  shows (0:R) = realZero
proof
  rfl
theorem annotated_order
  shows (0:R) < (1:R)
proof
  exact realZero.lt_one

end User.AnnotatedReal
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "AnnotatedReal.g17", source }], [library]);
  for (const name of loaded.at(-1)!.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
  const conflict = `module User.BadAnnotation
namespace User.BadAnnotation
import Grace.Cumulus.Real.Analysis.Sequences
theorem bad (n : Nat)
  shows (n:R) = n
proof
  rfl

end User.BadAnnotation
`;
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(),
    [{ file: "BadAnnotation.g17", source: conflict }], [library]),
  /already has type Nat/);
});

test("Heine-Cantor accepts a graph whose domain is exactly the interval", () => {
  const kernel = createZfgKernel();
  const file = new URL("../examples/DomainHeineErgo.g17", import.meta.url);
  const source = readFileSync(file, "utf8");
  const loaded = loadModuleSourceGraph(kernel, [{ file: "DomainHeineErgo.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, ["DomainHeineErgo.constant_interval_uniform"]);
});

test("non-strict order notation selects natural and real relations", () => {
  const kernel = createZfgKernel();
  const source = `module User.OrderNotation
namespace User.OrderNotation
import Grace.Cumulus.Real

lemma natural.zero_le (n : Nat)
  shows 0 ≤ n
proof
  exact _root_.Grace.Core.Nat.Order.LessEqual.zero at n with assumption

lemma real.square_nonnegative (A : Real)
  shows 0 ≤ A * A
proof
  exact realMulValue.square_nonnegative at A with assumption

lemma real.square_zero (A : Real)
  shows A * A = 0 ↔ A = 0
proof
  exact realMulValue.square_eq_zero_iff at A with assumption

end User.OrderNotation
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "OrderNotation.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.OrderNotation.natural.zero_le",
    "User.OrderNotation.real.square_nonnegative",
    "User.OrderNotation.real.square_zero",
  ]);
});

test("a fresh Main buffer accepts spaced finiteness formulas", () => {
  const kernel = createZfgKernel();
  const source = `module User.Scratch
namespace User.Scratch
import Grace.Cumulus.Main

theorem omega_big
  shows ¬ (Finite (ω))
proof
  exact omega.infinite

end User.Scratch
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "Scratch.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, ["User.Scratch.omega_big"]);
});

test("exact? finds an imported theorem whose whole statement is a negation", () => {
  const kernel = createZfgKernel();
  const source = `module User.SearchDemo
namespace User.SearchDemo
import Grace.Cumulus.Main

theorem omega_big
  shows ¬Finite(ω)
proof
  exact?

end User.SearchDemo
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "SearchDemo.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, ["User.SearchDemo.omega_big"]);
  const trace = kernel.theoremTacticTraces.get("User.SearchDemo.omega_big")!;
  assert.match(trace.steps[0]?.info?.items[0] ?? "", /exact omega\.infinite/);
});

test("subject entrypoints inherit their public prelude", () => {
  const kernel = createZfgKernel();
  const source = `module User.NumberTheoryDemo
namespace User.NumberTheoryDemo
import Grace.Cumulus.NumberTheory

lemma a_larger_prime (n : Nat)
  shows exists p, Prime(p) and n < p
proof
  exact Euclid.larger_prime at n

end User.NumberTheoryDemo
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "NumberTheoryDemo.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, ["User.NumberTheoryDemo.a_larger_prime"]);
});

test("ring and arith produce checked arithmetic proofs", () => {
  const kernel = createZfgKernel();
  const source = `module User.AutomationDemo
namespace User.AutomationDemo
import Grace.Cumulus.Nat

theorem polynomial.shuffle (a b c d : Nat)
  shows (a + b) + (c + d) = (a + c) + (b + d)
proof
  ring

theorem polynomial.distribute (a b c : Nat)
  shows (a + b) * c = a * c + b * c
proof
  ring

theorem polynomial.binomial (a b c d : Nat)
  shows (a + b) * (c + d) = a * c + a * d + (b * c + b * d)
proof
  ring

theorem polynomial.square (a b : Nat)
  shows (a + b) * (a + b) = a * a + a * b + (b * a + b * b)
proof
  ring

theorem polynomial.factor (a c d : Nat)
  shows a * c + a * d = a * (c + d)
proof
  ring

theorem polynomial.coefficients (a b c : Nat)
  shows (a + a) * (b + c) = a * b + a * c + (a * b + a * c)
proof
  ring

theorem polynomial.factor_order (a b c : Nat)
  shows a * (b * c) = c * (a * b)
proof
  ring

theorem polynomial.successor_product (k n : Nat)
  shows succ(k) * n = k * n + n
proof
  ring

theorem polynomial.successor_quotient_shape (a b k n D : Nat)
  shows ((n * D) * D) * (D * a + succ(k) * n) +
      (n * D) * (D * (D * b)) =
    (n * D) * (D * (D * a + k * n) + n * D) +
      ((n * D) * D) * (D * b)
proof
  ring

theorem polynomial.zero_quotient_shape (a b k n D : Nat)
  shows (D * a + n * 0) * (b + k) = a * D * b + a * D * k
proof
  ring

theorem polynomial.linear_combination (a b c d e f k m n : Nat)
  requires h1 : n * a + m * d = m * c + n * b
  requires h2 : k * c + n * f = n * e + k * d
  shows n * (k * a + m * f) = n * (m * e + k * b)
proof
  linear_combination k * h1 + m * h2

theorem polynomial.signed_linear_combination (a b c d e : Nat)
  requires h1 : a + c = b + c
  requires h2 : d = e
  shows a + e = b + d
proof
  linear_combination h1 - h2

theorem polynomial.composite_coefficient (a b c d : Nat)
  requires h : a = b
  shows (c + d) * a = (c + d) * b
proof
  linear_combination (c + d) * h

theorem polynomial.normalize_hypothesis (a b c d : Nat)
  requires h : (a + b) * c = d
  shows a * c + b * c = d
proof
  ring at h
  exact h

theorem polynomial.normalize_predicate_hypothesis (a b c d : Nat)
  requires h : (a + b) * c < d
  shows a * c + b * c < d
proof
  ring_nf at h
  exact h

theorem polynomial.normalize_predicate_goal (a b c d : Nat)
  requires h : a * c + b * c < d
  shows (a + b) * c < d
proof
  ring_nf
  exact h

theorem addition.cancel_right (a b c : Nat)
  requires h : a + c = b + c
  shows a = b
proof
  arith

theorem addition.cancel_left (a b c : Nat)
  requires h : c + a = c + b
  shows a = b
proof
  arith

theorem addition.cancel_offset (a b : Nat)
  requires h : a + 37 = b + 37
  shows a = b
proof
  arith

theorem addition.cancel_nested (a b c d : Nat)
  requires h : (a + c) + d = (b + c) + d
  shows a = b
proof
  arith

theorem addition.cancel_chain (a b c d e : Nat)
  requires h1 : a + c = b + c
  requires h2 : b + d = e + d
  shows a = e
proof
  arith

theorem addition.cancel_left_chain (a b c d e : Nat)
  requires h1 : c + a = c + b
  requires h2 : d + b = d + e
  shows a = e
proof
  arith

theorem addition.normalize (x : Nat)
  shows x + 0 = x
proof
  arith

theorem addition.congruence (x y z : Nat)
  requires h : x = y
  shows x + z = y + z
proof
  arith

theorem addition.affine_equality (x y : Nat)
  requires h : x + 1 = y
  shows 2 * x + 2 = 2 * y
proof
  arith

theorem bounds.antisymmetric (x y : Nat)
  requires hxy : x ≤ y
  requires hyx : y ≤ x
  shows x = y
proof
  arith

theorem bounds.unrelated_contradiction (a b x y : Nat)
  requires hxy : x < y
  requires hyx : y ≤ x
  shows a ≤ b
proof
  arith

theorem bounds.strict_sum (x y : Nat)
  requires hx : x > 2
  requires hy : y > 3
  shows x + y > 5
proof
  arith

theorem bounds.strict_weak_sum (x y : Nat)
  requires hx : x > 2
  requires hy : y ≥ 3
  shows x + y > 5
proof
  arith

theorem bounds.weak_strict_sum (x y : Nat)
  requires hx : x ≥ 2
  requires hy : y > 3
  shows x + y > 5
proof
  arith

theorem bounds.weak_sum (x y : Nat)
  requires hx : x ≥ 2
  requires hy : y ≥ 3
  shows x + y ≥ 5
proof
  arith

theorem bounds.three_terms (x y z : Nat)
  requires hx : x > 2
  requires hy : y ≥ 3
  requires hz : z > 4
  shows x + y + z > 9
proof
  arith

theorem bounds.small_coefficients (x y : Nat)
  requires hx : x > 2
  requires hy : y ≥ 3
  shows x + x + y > 7
proof
  arith

theorem bounds.weakened_strict_sum (x y : Nat)
  requires hx : x > 3
  requires hy : y > 2
  shows x + y > 4
proof
  arith

theorem bounds.sharp_strict_sum (x y : Nat)
  requires hx : x > 2
  requires hy : y > 3
  shows x + y > 6
proof
  arith

theorem bounds.strict_implies_weak (x y : Nat)
  requires h : x > y
  shows x ≥ y
proof
  arith

theorem bounds.linarith_spelling (x y z : Nat)
  requires hxy : x ≤ y + 2
  requires hyz : y < z
  shows x < z + 3
proof
  linarith

theorem bounds.affine_chain (x y z : Nat)
  requires hxy : x ≤ y + 2
  requires hyz : y ≤ z + 3
  shows x ≤ z + 5
proof
  arith

theorem bounds.integral_rounding (x : Nat)
  requires h : 2 * x ≤ 1
  shows x ≤ 0
proof
  arith

theorem simp.closed_boolean
  shows BoolOps.not(BoolOps.not(Bool.true)) = Bool.true
proof
  simp

theorem simp.constructive_tautology (x y : Set)
  requires h : x = x and y = y
  shows y = y and x = x
proof
  simp

theorem simp.orients_occurs_check (x : Set)
  requires h : x = orderedPair(x, x)
  shows orderedPair(x, x) = x
proof
  simp

theorem logic.excluded_middle (x y : Set)
  shows x = y or not x = y
proof
  tauto

theorem logic.peirce (x y z w : Set)
  shows ((x = y -> z = w) -> x = y) -> x = y
proof
  tauto

theorem equality.congruence_closure (x y z : Set)
  requires hxy : x = y
  requires hyz : y = z
  shows orderedPair(singleton(x), x) = orderedPair(singleton(z), z)
proof
  cc

theorem equality.predicate_transport (x y A : Set)
  requires hxy : x = y
  requires hx : x in A
  shows y in A
proof
  congruence

end User.AutomationDemo
`;
  const loaded = loadModuleSourceGraph(kernel, [{ file: "AutomationDemo.g17", source }], [library]);
  assert.deepEqual(loaded.at(-1)?.theorems, [
    "User.AutomationDemo.polynomial.shuffle",
    "User.AutomationDemo.polynomial.distribute",
    "User.AutomationDemo.polynomial.binomial",
    "User.AutomationDemo.polynomial.square",
    "User.AutomationDemo.polynomial.factor",
    "User.AutomationDemo.polynomial.coefficients",
    "User.AutomationDemo.polynomial.factor_order",
    "User.AutomationDemo.polynomial.successor_product",
    "User.AutomationDemo.polynomial.successor_quotient_shape",
    "User.AutomationDemo.polynomial.zero_quotient_shape",
    "User.AutomationDemo.polynomial.linear_combination",
    "User.AutomationDemo.polynomial.signed_linear_combination",
    "User.AutomationDemo.polynomial.composite_coefficient",
    "User.AutomationDemo.polynomial.normalize_hypothesis",
    "User.AutomationDemo.polynomial.normalize_predicate_hypothesis",
    "User.AutomationDemo.polynomial.normalize_predicate_goal",
    "User.AutomationDemo.addition.cancel_right",
    "User.AutomationDemo.addition.cancel_left",
    "User.AutomationDemo.addition.cancel_offset",
    "User.AutomationDemo.addition.cancel_nested",
    "User.AutomationDemo.addition.cancel_chain",
    "User.AutomationDemo.addition.cancel_left_chain",
    "User.AutomationDemo.addition.normalize",
    "User.AutomationDemo.addition.congruence",
    "User.AutomationDemo.addition.affine_equality",
    "User.AutomationDemo.bounds.antisymmetric",
    "User.AutomationDemo.bounds.unrelated_contradiction",
    "User.AutomationDemo.bounds.strict_sum",
    "User.AutomationDemo.bounds.strict_weak_sum",
    "User.AutomationDemo.bounds.weak_strict_sum",
    "User.AutomationDemo.bounds.weak_sum",
    "User.AutomationDemo.bounds.three_terms",
    "User.AutomationDemo.bounds.small_coefficients",
    "User.AutomationDemo.bounds.weakened_strict_sum",
    "User.AutomationDemo.bounds.sharp_strict_sum",
    "User.AutomationDemo.bounds.strict_implies_weak",
    "User.AutomationDemo.bounds.linarith_spelling",
    "User.AutomationDemo.bounds.affine_chain",
    "User.AutomationDemo.bounds.integral_rounding",
    "User.AutomationDemo.simp.closed_boolean",
    "User.AutomationDemo.simp.constructive_tautology",
    "User.AutomationDemo.simp.orients_occurs_check",
    "User.AutomationDemo.logic.excluded_middle",
    "User.AutomationDemo.logic.peirce",
    "User.AutomationDemo.equality.congruence_closure",
    "User.AutomationDemo.equality.predicate_transport",
  ]);

  // Classical case analysis is part of the ground procedure, so excluded middle closes.
  assert.equal(loadModuleSourceGraph(createZfgKernel(), [{ file: "ClassicalSimp.g17", source: `
module User.ClassicalSimp
namespace User.ClassicalSimp
import Grace.Cumulus.Main
theorem excluded_middle (x y : Set)
  shows x = y or not x = y
proof
  simp

end User.ClassicalSimp
` }], [library]).at(-1)?.theorems.length, 1);

  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "FalseRing.g17", source: `
module User.FalseRing
namespace User.FalseRing
import Grace.Cumulus.Nat
theorem false_ring (a b : Nat)
  shows a + b = a
proof
  ring

end User.FalseRing
` }], [library]), /settle did not close this goal/);

  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "FalseArith.g17", source: `
module User.FalseArith
namespace User.FalseArith
import Grace.Cumulus.Nat
theorem false_arith (a b : Nat)
  shows a = b
proof
  arith

end User.FalseArith
` }], [library]), /arith found no supported linear arithmetic step/);

  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "FalseInequality.g17", source: `
module User.FalseInequality
namespace User.FalseInequality
import Grace.Cumulus.Nat
theorem false_inequality (x y : Nat)
  requires hx : x > 2
  requires hy : y > 3
  shows x + y > 7
proof
  arith

end User.FalseInequality
` }], [library]), /arith found no linear arithmetic contradiction/);
});

test("the CLI accepts multiple module roots for Cumulus", () => {
  const run = spawnSync(process.execPath, ["bin/g17.ts", "check", "--json",
    "--module-root", "lib", "lib/Grace/Cumulus.g17"], {
    cwd: project, encoding: "utf8", maxBuffer: 16 * 1024 * 1024,
  });
  assert.equal(run.status, 0, run.stderr);
  const report = JSON.parse(run.stdout);
  assert.equal(report.ok, true);
  assert.ok(report.checked.some((item: { file: string }) => item.file.endsWith("lib/Grace/Cumulus/Order.g17")));
});

test("the independent Python checker replays the complete Cumulus machine module", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-cumulus-python-"));
  const machine = join(directory, "Cumulus.g17m");
  const environment = join(directory, "Cumulus.g17env");
  const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile",
    "--module-root", "lib", "lib/Grace/Cumulus.g17",
    "--out", machine, "--environment", environment], { cwd: project, encoding: "utf8" });
  assert.equal(compile.status, 0, compile.stderr);
  const checked = spawnSync("python3", ["checkers/python/g17check.py", machine,
    "--environment", environment, "--json"], { cwd: project, encoding: "utf8" });
  assert.equal(checked.status, 0, checked.stderr);
  const report = JSON.parse(checked.stdout);
  assert.equal(report.ok, true);
  const compiled = compile.stdout.match(/compiled (\d+) theorems.*\((\d+) instructions,/);
  assert.ok(compiled, compile.stdout);
  assert.equal(report.theorems, Number(compiled[1]));
  assert.equal(report.instructions, Number(compiled[2]));
});
