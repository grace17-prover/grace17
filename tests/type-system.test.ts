// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import {
  app, nat, forall, imp, checkSoftType, classReport, createZfgKernel, elaborateModule, formulaEquals,
  inferSoftTypes, instanceReport, InstanceResolutionError, loadModuleGraph, pred, prepareInstanceProver,
  softTypeReport, SoftTypeError, termEquals, v, prepareRefinementProver,
} from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const core = fileURLToPath(new URL("../lib/Grace/Core.g17", import.meta.url));
const setLibrary = fileURLToPath(new URL("../lib/Grace/Cumulus/Set.g17", import.meta.url));

test("Tau composes certified signatures into a checked soft-type proof", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [core, setLibrary], [root]);
  const assumptions = [pred("Nat", v("k")), pred("Nat", v("y")), pred("Nat", v("z"))];
  const product = app("Grace.Core.Nat.Rec.mul", v("k"), v("y"));
  const term = app("Grace.Core.Nat.Rec.add", product, v("z"));
  const proof = checkSoftType(kernel, term, "Nat", assumptions);
  assert.ok(formulaEquals(kernel.checkProof(proof, assumptions), pred("Nat", term)));
  assert.deepEqual(inferSoftTypes(kernel, term, assumptions).map(item => item.predicate), [
    "Grace.Cumulus.Set.Classes.Class.Natural", "Grace.Cumulus.Set.Ordinal.Ordinal",
    "Grace.Cumulus.Set.Ordinal.Transitive", "Nat",
  ]);
  assert.ok(softTypeReport(kernel).some(rule => rule.name.endsWith("mul.closed") && rule.conclusion.predicate === "Nat"));
  const numeral = nat(42);
  const numeralProof = checkSoftType(kernel, numeral, "Nat");
  assert.ok(formulaEquals(kernel.checkProof(numeralProof), pred("Nat", numeral)),
    "bounded refinement search must retain ordinary numeral constructor proofs");
});

test("Tau introduces transparent soft-type aliases from carrier membership", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module TransparentCarrier
namespace TransparentCarrier
def Q : Set := ω
class Rational (q : Set) := q ∈ Q

theorem membership_is_rational (q : Set)
  requires qInQ : q ∈ Q
  shows Rational(q)
proof
  typecheck

end TransparentCarrier
`);
  assert.deepEqual(result.theorems, ["TransparentCarrier.membership_is_rational"]);
  const alias = softTypeReport(kernel).find(rule =>
    rule.name === "TransparentCarrier.Rational.equation.tau_alias");
  assert.equal(alias?.premises[0]?.predicate, "in");
  assert.equal(alias?.conclusion.predicate, "TransparentCarrier.Rational");
});

test("soft-type failures expose deterministic diagnostics", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [core, setLibrary], [root]);
  const term = app("pair", app("empty"), app("empty"));
  assert.throws(() => checkSoftType(kernel, term, "Nat"), (error: unknown) => {
    assert.ok(error instanceof SoftTypeError);
    assert.equal(error.diagnostic.expected, "Nat");
    assert.deepEqual(error.diagnostic.inferred, []);
    assert.ok(error.diagnostic.candidateRules.some(name => name.endsWith("add.closed")));
    return true;
  });
});

test("classes elaborate to predicates but are rejected as set terms", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [core, setLibrary], [root]);
  assert.deepEqual(classReport(kernel).map(item => item.name), [
    "Grace.Cumulus.Set.Classes.Class.Inhabited",
    "Grace.Cumulus.Set.Classes.Class.MemberOf",
    "Grace.Cumulus.Set.Classes.Class.Natural",
    "Grace.Cumulus.Set.Classes.Class.SubsetsOf",
    "Grace.Cumulus.Set.Classes.Class.Universe",
    "Grace.Cumulus.Set.Hierarchy.CumulativeUniverse",
    "Grace.Cumulus.Set.Hierarchy.FiniteStage",
    "Grace.Cumulus.Set.Hierarchy.Ranked",
    "Grace.Cumulus.Set.Ordinal.Ordinal",
  ]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Classes.Class.Universe.membership"));
  assert.ok(kernel.theorems.has("Grace.Cumulus.Set.Classes.Class.SubsetsOf.Universe"));
  const subsetsOf = classReport(kernel).find(item => item.name.endsWith("Class.SubsetsOf"));
  assert.deepEqual(subsetsOf?.parameterTypes, ["Class"]);
  assert.equal(kernel.predicates.has("Grace.Cumulus.Set.Classes.Class.SubsetsOf"), false);
  assert.doesNotMatch(
    JSON.stringify(kernel.theorems.get("Grace.Cumulus.Set.Classes.Class.SubsetsOf.Universe")),
    /\$class:/,
  );
  assert.throws(() => elaborateModule(kernel, `
module BadClassUse
namespace BadClassUse
import Grace.Cumulus.Set.Classes
open Grace.Cumulus.Set.Classes.Class
def bad (x : Set) : Set := Natural

end BadClassUse
`), /class Natural is not a Set; use class membership or bounded realization/);
});

test("class operators coerce sets to classes and class equality is extensional", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module ClassOperators
namespace ClassOperators
predicate Subset (X A : Set) := forall x, x in X -> x in A
class Universe (x : Set) := { x | x = x }
class SubsetsOf (A : Class) := { X : Set | forall x, x in X -> x ∈ A }
class Meets (A : Class) := { X : Set | exists x, x in X and x ∈ A }
theorem SubsetsOf.set_characterization (X A : Set)
  shows X ∈ SubsetsOf(A) <-> Subset(X, A)
proof
  settle with Subset
theorem SubsetsOf.Universe
  shows SubsetsOf(Universe) = Universe
proof
  settle with Universe
theorem Meets.capture_safe (x X : Set)
  shows X ∈ Meets(x) <-> exists y, y in X and y in x
proof
  settle

end ClassOperators
`);
  assert.deepEqual(result.theorems, [
    "ClassOperators.SubsetsOf.set_characterization",
    "ClassOperators.SubsetsOf.Universe",
    "ClassOperators.Meets.capture_safe",
  ]);
  assert.doesNotMatch(JSON.stringify(kernel.theorems.get("ClassOperators.SubsetsOf.Universe")), /\$class:/);
});

test("unbounded class comprehensions support explicit elements and parameters", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module ClassComprehension
namespace ClassComprehension
class Universe (x : Set) := { x | x = x }
class Avoids (A : Set) := { x : Set | not (x in A) }
theorem Universe.membership (x : Set)
  shows x ∈ Universe <-> x = x
proof
  settle with Universe
theorem Avoids.membership (x A : Set)
  shows x ∈ Avoids(A) <-> not (x in A)
proof
  settle with Avoids

end ClassComprehension
`);
  assert.deepEqual(result.theorems, [
    "ClassComprehension.Universe.membership",
    "ClassComprehension.Avoids.membership",
  ]);
  assert.deepEqual(classReport(kernel).map(item => ({
    name: item.name, element: item.element, parameters: item.parameters,
  })), [
    { name: "ClassComprehension.Avoids", element: "x", parameters: ["A"] },
    { name: "ClassComprehension.Universe", element: "x", parameters: [] },
  ]);
  assert.throws(() => elaborateModule(kernel, `
module BadUniverseUse
namespace BadUniverseUse
import ClassComprehension
def everything (x : Set) : Set := ClassComprehension.Universe

end BadUniverseUse
`), /class ClassComprehension\.Universe is not a Set/);
});

test("class comprehensions diagnose missing and conflicting element binders", () => {
  assert.throws(() => elaborateModule(createZfgKernel(), `
class MissingType := { x | x = x }
`), /class comprehension variable x needs a type/);
  assert.throws(() => elaborateModule(createZfgKernel(), `
class Conflict (x : Nat) := { x : Set | x = x }
`), /class comprehension variable x has conflicting types Nat and Set/);
});

test("named requirements and obtain retain source-level proof states", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [core], [root]);
  const trace = kernel.theoremTacticTraces.get("Grace.Core.Nat.Order.LessEqual.transitive");
  assert.ok(trace?.steps.some(step => step.command === "obtain ⟨k, hk⟩ := hab"));
  assert.ok(trace?.initial.goals[0]?.locals.some(local => local.name === "hab"));
});

test("instance resolution handles deep chains with indexed, memoized search", () => {
  const kernel = createZfgKernel();
  const depth = 48;
  const declarations = Array.from({ length: depth + 1 }, (_, index) =>
    `predicate P${index} (x : Set) := x = x`).join("\n");
  const instances = Array.from({ length: depth }, (_, index) => `
instance step_${index + 1} (x : Set)
  requires previous : P${index}(x)
  shows P${index + 1}(x)
proof
  unfold P${index + 1}
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceDepth
namespace InstanceDepth
${declarations}
def witness : Set := empty
instance base
  shows P0(witness)
proof
  unfold P0
  rfl
${instances}

end InstanceDepth
`);
  const names = new Set(instanceReport(kernel).map(item => item.name));
  const prover = prepareInstanceProver(kernel, names);
  const proof = prover.prove(app("InstanceDepth.witness"), `InstanceDepth.P${depth}`);
  assert.ok(proof);
  assert.ok(formulaEquals(kernel.checkProof(proof!),
    pred(`InstanceDepth.P${depth}`, app("InstanceDepth.witness"))));
  assert.deepEqual(prover.stats(), {
    goalsVisited: depth + 1,
    memoHits: 0,
    rulesConsidered: depth + 1,
    successfulCandidates: depth + 1,
    maximumDepth: depth,
  });
});

test("instance indexing skips a large irrelevant registry", () => {
  const kernel = createZfgKernel();
  const irrelevantCount = 512;
  const irrelevant = Array.from({ length: irrelevantCount }, (_, index) => `
predicate Noise${index} (x : Set) := x = x
instance noise_${index}
  shows Noise${index}(empty)
proof
  unfold Noise${index}
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceIndex
namespace InstanceIndex
predicate Wanted (x : Set) := x = x
instance wanted
  shows Wanted(empty)
proof
  unfold Wanted
  rfl
${irrelevant}

end InstanceIndex
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  assert.ok(prover.prove(app("empty"), "InstanceIndex.Wanted"));
  const stats = prover.stats();
  assert.equal(stats.rulesConsidered, 1);
  assert.equal(stats.goalsVisited, 1);
  assert.equal(instanceReport(kernel).length, irrelevantCount + 1);
});

test("instance resolution synthesizes deterministic output parameters", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module InstanceOutputs
namespace InstanceOutputs
predicate HasOperation (carrier operation : Set) := carrier = carrier
def reals : Set := empty
def realAdd : Set := pair(empty, empty)
instance real_add
  shows HasOperation(reals, realAdd)
proof
  unfold HasOperation
  rfl
instance pointwise (carrier : Set)
  shows HasOperation(pair(carrier, carrier), pair(carrier, carrier))
proof
  unfold HasOperation
  rfl

end InstanceOutputs
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  const real = prover.resolve("InstanceOutputs.HasOperation", [
    app("InstanceOutputs.reals"), undefined,
  ]);
  assert.ok(real);
  assert.equal(real.instance, "InstanceOutputs.real_add");
  assert.ok(termEquals(real.arguments[1]!, app("InstanceOutputs.realAdd")));
  assert.ok(formulaEquals(kernel.checkProof(real.proof), pred(
    "InstanceOutputs.HasOperation", app("InstanceOutputs.reals"), app("InstanceOutputs.realAdd"))));

  const emptyPair = app("pair", app("empty"), app("empty"));
  const generic = prover.resolve("InstanceOutputs.HasOperation", [emptyPair, undefined]);
  assert.ok(generic);
  assert.ok(termEquals(generic.arguments[1]!, emptyPair));
});

test("instance output synthesis rejects competing implementations", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module InstanceOutputAmbiguity
namespace InstanceOutputAmbiguity
predicate HasZero (carrier zero : Set) := carrier = carrier
def carrier : Set := empty
def firstZero : Set := empty
def secondZero : Set := pair(empty, empty)
instance first
  shows HasZero(carrier, firstZero)
proof
  unfold HasZero
  rfl
instance second
  shows HasZero(carrier, secondZero)
proof
  unfold HasZero
  rfl

end InstanceOutputAmbiguity
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  assert.throws(() => prover.resolve("InstanceOutputAmbiguity.HasZero", [
    app("InstanceOutputAmbiguity.carrier"), undefined,
  ]), /ambiguous instance.*first.*second/);
});

test("instance output synthesis indexes wide registries and memoizes repeated queries", () => {
  const kernel = createZfgKernel();
  const count = 512;
  const instances = Array.from({ length: count }, (_, index) => `
def carrier_${index} : Set := pair(${index}, ${index})
def operation_${index} : Set := pair(${index + 1}, ${index + 1})
instance operation_${index}_instance
  shows HasOperation(carrier_${index}, operation_${index})
proof
  unfold HasOperation
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceOutputIndex
namespace InstanceOutputIndex
predicate HasOperation (carrier operation : Set) := carrier = carrier
${instances}

end InstanceOutputIndex
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  const query = [app(`InstanceOutputIndex.carrier_${count - 1}`), undefined] as const;
  const first = prover.resolve("InstanceOutputIndex.HasOperation", query);
  assert.ok(first);
  assert.equal(prover.stats().rulesConsidered, 1);
  assert.equal(prover.stats().goalsVisited, 1);
  const second = prover.resolve("InstanceOutputIndex.HasOperation", query);
  assert.ok(second);
  assert.equal(prover.stats().rulesConsidered, 1);
  assert.equal(prover.stats().memoHits, 1);
});

test("instance search tables diamonds, terminates cycles, and enforces limits", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module InstanceGraph
namespace InstanceGraph
predicate P (x : Set) := x = x
predicate Q (x : Set) := x = x
predicate R (x : Set) := x = x
predicate S (x : Set) := x = x
instance base
  shows P(empty)
proof
  unfold P
  rfl
instance p_q (x : Set)
  requires h : P(x)
  shows Q(x)
proof
  unfold Q
  rfl
instance p_r (x : Set)
  requires h : P(x)
  shows R(x)
proof
  unfold R
  rfl
instance qr_s (x : Set)
  requires hq : Q(x)
  requires hr : R(x)
  shows S(x)
proof
  unfold S
  rfl

end InstanceGraph
`);
  const names = new Set(instanceReport(kernel).map(item => item.name));
  const prover = prepareInstanceProver(kernel, names);
  assert.ok(prover.prove(app("empty"), "InstanceGraph.S"));
  assert.ok(prover.stats().memoHits >= 1, "the shared P(empty) subgoal should be tabled");

  const expanding = createZfgKernel();
  elaborateModule(expanding, `
module InstanceLimit
namespace InstanceLimit
predicate P (x : Set) := x = x
instance expand (x : Set)
  requires next : P(pair(x, x))
  shows P(x)
proof
  unfold P
  rfl

end InstanceLimit
`);
  const limited = prepareInstanceProver(expanding,
    new Set(instanceReport(expanding).map(item => item.name)), [], [], { maximumDepth: 12 });
  assert.throws(() => limited.prove(app("empty"), "InstanceLimit.P"), /maximumDepth/);
});

test("exact local evidence wins before deterministic global ambiguity", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module InstanceAmbiguity
namespace InstanceAmbiguity
predicate P (x : Set) := x = x
instance zulu
  shows P(empty)
proof
  unfold P
  rfl
instance alpha
  shows P(empty)
proof
  unfold P
  rfl

end InstanceAmbiguity
`);
  const names = new Set(instanceReport(kernel).map(item => item.name).reverse());
  const ambiguous = prepareInstanceProver(kernel, names);
  assert.throws(() => ambiguous.prove(app("empty"), "InstanceAmbiguity.P"), (error: unknown) => {
    assert.ok(error instanceof InstanceResolutionError);
    assert.deepEqual(error.diagnostic.candidates, [
      "InstanceAmbiguity.alpha", "InstanceAmbiguity.zulu",
    ]);
    return true;
  });

  const wanted = pred("InstanceAmbiguity.P", app("empty"));
  const local = prepareInstanceProver(kernel, names, [wanted]);
  const proof = local.prove(app("empty"), "InstanceAmbiguity.P");
  assert.ok(proof);
  assert.ok(formulaEquals(kernel.checkProof(proof!, [wanted]), wanted));
  assert.equal(local.stats().rulesConsidered, 0);
  assert.equal(local.stats().goalsVisited, 0);
});

test("cyclic failure terminates and is memoized across repeated queries", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module InstanceCycle
namespace InstanceCycle
predicate P (x : Set) := x = x
predicate Q (x : Set) := x = x
instance q_to_p (x : Set)
  requires q : Q(x)
  shows P(x)
proof
  unfold P
  rfl
instance p_to_q (x : Set)
  requires p : P(x)
  shows Q(x)
proof
  unfold Q
  rfl

end InstanceCycle
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  assert.equal(prover.prove(app("empty"), "InstanceCycle.P"), undefined);
  const first = prover.stats();
  assert.deepEqual(first, {
    goalsVisited: 2,
    memoHits: 0,
    rulesConsidered: 2,
    successfulCandidates: 0,
    maximumDepth: 1,
  });
  assert.equal(prover.prove(app("empty"), "InstanceCycle.P"), undefined);
  assert.deepEqual(prover.stats(), { ...first, memoHits: 1 });
});

test("argument-head indexing skips same-class rigid instances", () => {
  const kernel = createZfgKernel();
  const count = 512;
  const declarations = Array.from({ length: count }, (_, index) => `
def token_${index} : Set := pair(empty, empty)
instance token_${index}_wanted
  shows Wanted(token_${index})
proof
  unfold Wanted
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceRigidIndex
namespace InstanceRigidIndex
predicate Wanted (x : Set) := x = x
${declarations}

end InstanceRigidIndex
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  assert.ok(prover.prove(app(`InstanceRigidIndex.token_${count - 1}`), "InstanceRigidIndex.Wanted"));
  assert.equal(prover.stats().rulesConsidered, 1);
  assert.equal(prover.stats().goalsVisited, 1);
});

test("instance discrimination tries index nested first-order structure", () => {
  const kernel = createZfgKernel();
  const count = 128;
  const declarations = Array.from({ length: count }, (_, index) => `
def token_${index} : Set := pair(${index}, ${index})
instance nested_${index}
  shows Wanted(pair(token_${index}, empty))
proof
  unfold Wanted
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceNestedIndex
namespace InstanceNestedIndex
predicate Wanted (x : Set) := x = x
${declarations}

end InstanceNestedIndex
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)));
  assert.ok(prover.prove(app("pair", app(`InstanceNestedIndex.token_${count - 1}`), app("empty")),
    "InstanceNestedIndex.Wanted"));
  assert.equal(prover.stats().rulesConsidered, 1);
});

test("same-head branching is stopped by the rule-attempt budget", () => {
  const kernel = createZfgKernel();
  const count = 32;
  const predicates = Array.from({ length: count }, (_, index) =>
    `predicate Missing${index} (x : Set) := x = x`).join("\n");
  const instances = Array.from({ length: count }, (_, index) => `
instance attempt_${index} (x : Set)
  requires missing : Missing${index}(x)
  shows Wanted(x)
proof
  unfold Wanted
  rfl`).join("\n");
  elaborateModule(kernel, `
module InstanceBranchLimit
namespace InstanceBranchLimit
predicate Wanted (x : Set) := x = x
${predicates}
${instances}

end InstanceBranchLimit
`);
  const prover = prepareInstanceProver(kernel,
    new Set(instanceReport(kernel).map(item => item.name)), [], [], { maximumRuleAttempts: 8 });
  assert.throws(() => prover.prove(app("empty"), "InstanceBranchLimit.Wanted"), /maximumRuleAttempts/);
  assert.equal(prover.stats().rulesConsidered, 9);
});


test("automatic refinements bound expanding terms and preserve explicit evidence", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module RefinementLimit
namespace RefinementLimit
predicate P (x : Set) := x = x
theorem expand (x : Set)
  requires next : P(pair(x, x))
  shows P(x)
proof
  unfold P
  rfl
end RefinementLimit
`);
  const term = app("empty");
  const known = v("known");
  const goal = pred("RefinementLimit.P", known);
  const prover = prepareRefinementProver(kernel, [goal]);
  const started = performance.now();
  assert.equal(prover.prove(term, "RefinementLimit.P"), undefined);
  assert.ok(performance.now() - started < 2000, "expanding refinement search must stop promptly");
  const evidence = prover.prove(known, "RefinementLimit.P");
  assert.ok(evidence);
  assert.ok(formulaEquals(kernel.checkProof(evidence, [goal]), goal));
});

test("local output synthesis deduplicates evidence but rejects different argument tuples", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module LocalOutputs
namespace LocalOutputs
predicate HasOperation (carrier operation : Set) := carrier = carrier
end LocalOutputs
`);
  const first = pred("LocalOutputs.HasOperation", v("C"), v("op"));
  const second = pred("LocalOutputs.HasOperation", v("C"), v("other"));
  const duplicate = { rule: "assumption" as const, formula: first };
  const prover = prepareInstanceProver(kernel, new Set(), [first], [duplicate, duplicate]);
  const resolved = prover.resolve("LocalOutputs.HasOperation", [v("C"), undefined]);
  assert.ok(resolved);
  assert.ok(termEquals(resolved.arguments[1]!, v("op")));
  assert.ok(formulaEquals(kernel.checkProof(resolved.proof, [first]), first));
  const ambiguous = prepareInstanceProver(kernel, new Set(), [first, second], [duplicate]);
  assert.throws(() => ambiguous.resolve("LocalOutputs.HasOperation", [v("C"), undefined]),
    /ambiguous instance/);
  const empty = prepareInstanceProver(kernel, new Set());
  assert.equal(empty.resolve("LocalOutputs.HasOperation", [v("C"), undefined]), undefined);
});

test("instance patterns match compound targets containing variables and numerals", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module CompoundInstance
namespace CompoundInstance
predicate HasOperation (carrier operation : Set) := carrier = carrier
instance any (C : Set)
  shows HasOperation(C, C)
proof
  unfold HasOperation
  rfl
end CompoundInstance
`);
  const names = new Set(instanceReport(kernel).map(item => item.name));
  const target = app("pair", v("x"), app("pair", nat(3), v("y")));
  const prover = prepareInstanceProver(kernel, names);
  const result = prover.resolve("CompoundInstance.HasOperation", [target, undefined]);
  assert.ok(result);
  assert.ok(termEquals(result.arguments[1]!, target));
  assert.ok(formulaEquals(kernel.checkProof(result.proof),
    pred("CompoundInstance.HasOperation", target, target)));
  assert.equal(prover.stats().rulesConsidered, 1);
});

test("instance output substitution leaves caller variables inside replacements intact", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module SimultaneousInstance
namespace SimultaneousInstance
predicate Related (left right : Set) := left = left
instance swap (x y : Set)
  shows Related(pair(x, y), pair(y, x))
proof
  unfold Related
  rfl
end SimultaneousInstance
`);
  const names = new Set(instanceReport(kernel).map(item => item.name));
  // x maps to pair(y, 3), while y maps to z. The free y inside the
  // replacement for x belongs to the caller and must remain y.
  const replacement = app("pair", v("y"), nat(3));
  const input = app("pair", replacement, v("z"));
  const output = app("pair", v("z"), replacement);
  const prover = prepareInstanceProver(kernel, names);
  const result = prover.resolve("SimultaneousInstance.Related", [input, undefined]);
  assert.ok(result);
  assert.ok(termEquals(result.arguments[1]!, output));
  assert.ok(formulaEquals(kernel.checkProof(result.proof),
    pred("SimultaneousInstance.Related", input, output)));
});


test("refinement search avoids checking unsatisfied rule applications", () => {
  const kernel = createZfgKernel();
  kernel.declarePredicate("Missing", 1);
  kernel.declarePredicate("Wanted", 1);
  kernel.addAxiom("conditional", forall("x", imp(pred("Missing", v("x")), pred("Wanted", v("x")))));
  const failed = prepareRefinementProver(kernel);
  const successful = prepareRefinementProver(kernel, [pred("Missing", v("a"))]);
  const original = kernel.checkProof.bind(kernel);
  let checks = 0;
  kernel.checkProof = (...args) => { checks += 1; return original(...args); };
  assert.equal(failed.prove(v("a"), "Wanted"), undefined);
  assert.equal(checks, 0);
  const proof = successful.prove(v("a"), "Wanted");
  assert.ok(proof);
  assert.ok(checks > 0, "successful applications remain kernel checked");
  assert.ok(formulaEquals(original(proof, [pred("Missing", v("a"))]), pred("Wanted", v("a"))));
});
