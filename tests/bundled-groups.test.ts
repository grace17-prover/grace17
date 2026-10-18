// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled groups: a group is a structure G with projections G.carrier, G.mul,
// G.one, G.inv; under a hypothesis Group(G) the operation is written
// a * b and the inverse a⁻¹, a binder (a b : G) is membership in the
// carrier, memberships of compound terms are synthesized, the group rewrite
// set closes the textbook identities, and statements print back in the same
// notation. The typed `*` of the naturals keeps its meaning inside a group
// section and `*` outside one.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfgKernel, createZfKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, rememberFailureDisplay, workbenchFailure } from "../src/workbench.ts";

const header = "module BundledGroups\nimport Grace.Cumulus.Algebra.Group.Basic\nimport Grace.Cumulus.Nat.Core\n";

const section = (body: string) => header + `
section S
variable (G : Set)
hypothesis group : Group(G)
${body}
end S
`;

function load(source: string, foundation: "ZF" | "ZFG" = "ZF") {
  const kernel = foundation === "ZF" ? createZfKernel() : createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledGroups.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledGroups.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

test("a * b, a⁻¹, and (a b : G) are call2(G.mul, a, b), apply(G.inv, a), and a ∈ G.carrier", () => {
  const written = load(section(`
theorem cancel (a b : G)
  shows a⁻¹ * (a * b) = b
proof
  exact inv_mul_cancel_left with *
`));
  const spelled = load(header + `
theorem cancel (G a b : Set)
  requires aIn : a ∈ G.carrier
  requires bIn : b ∈ G.carrier
  requires group : Group(G)
  shows call2(G.mul, apply(G.inv, a), call2(G.mul, a, b)) = b
proof
  exact inv_mul_cancel_left with *
`);
  assert.ok(formulaEquals(written.theorems.get("BundledGroups.cancel")!, spelled.theorems.get("BundledGroups.cancel")!));
});

test("the statement and a remaining goal print with *, ⁻¹, and the carrier binders", () => {
  const result = check(section(`
theorem rev (a b : G)
  shows (a * b)⁻¹ = b⁻¹ * a⁻¹
proof
  exact mul_inv_rev with *
`));
  const statement = result.theorems.find(item => item.name === "BundledGroups.rev")!.statement;
  assert.equal(statement, "∀ G, ∀ (a b : G), Group(G) → (a * b)⁻¹ = b⁻¹ * a⁻¹");
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "BundledGroups.g17", source: section(`
theorem open (a b : G)
  shows (a⁻¹)⁻¹ * (a * b) = b
proof
  have twice : (a⁻¹)⁻¹ = a := inv_inv with *
  exact twice
`) }], ["lib"]);
    assert.fail("the proof should not check");
  } catch (error) {
    assert.ok(error instanceof SurfaceError);
    rememberFailureDisplay(error, kernel);
    const goal = workbenchFailure(error).trace!.steps.at(-1)!.after.goals[0]!;
    assert.equal(goal.goal, "(a⁻¹)⁻¹ * (a * b) = b");
    assert.equal(goal.locals.find(item => item.name === "twice")!.formula, "(a⁻¹)⁻¹ = a");
    assert.deepEqual(goal.assumptions.filter(item => /∈ G$/u.test(item)), ["a ∈ G", "b ∈ G"]);
  }
});

test("memberships of compound terms are synthesized, and with *, typecheck, and cc see the binder guards", () => {
  check(section(`
theorem closed (a b : G)
  shows a * b⁻¹ ∈ G.carrier
proof
  synthesize

theorem typed (a b c : G)
  shows (a * b) * c⁻¹ * G.one ∈ G.carrier
proof
  typecheck

theorem assumed (a : G)
  shows a ∈ G.carrier
proof
  assumption

theorem applied (a b c : G)
  shows a * b * c = a * (b * c)
proof
  exact mul_assoc with *
`));
});

test("the group rewrite set closes the textbook identities, with side conditions discharged from the binders", () => {
  check(section(`
theorem simplified (a b c : G)
  shows a * (b * b⁻¹) * (G.one * c) = a * c
proof
  group_simp

theorem conjugate (a b : G)
  shows a * b * a⁻¹ * (a * b⁻¹ * a⁻¹) = G.one
proof
  group_simp

theorem rewritten (a b : G)
  shows (a * b)⁻¹ * (a * b) = G.one
proof
  rw Group.inv_mul
  rfl
`));
});

test("the typed * of the naturals is kept inside a group section, and * outside one falls back to natural multiplication", () => {
  const inside = load(section(`
theorem natural (n m : Nat)
  shows n * m = m * n
proof
  exact mul.commutative at m, n
`));
  const spelled = load(header + `
theorem natural (G : Set) (n m : Nat)
  requires group : Group(G)
  shows mul(n, m) = mul(m, n)
proof
  exact mul.commutative at m, n
`);
  assert.ok(formulaEquals(inside.theorems.get("BundledGroups.natural")!, spelled.theorems.get("BundledGroups.natural")!));
  check(header + `
theorem outside
  shows 2 * 3 = 6
proof
  compute
`);
  const bare = load(header + `
theorem bare (x y : Set)
  shows x * y = y * x
proof
  sorry
`);
  const natural = load(header + `
theorem bare (x y : Set)
  shows mul(x, y) = mul(y, x)
proof
  sorry
`);
  assert.ok(formulaEquals(bare.theorems.get("BundledGroups.bare")!, natural.theorems.get("BundledGroups.bare")!));
});

test("an abelian hypothesis supplies the same notation, and the bridges relate the bundled and unbundled forms", () => {
  check(header + `
section A
variable (G : Set)
hypothesis abelian : AbelianGroup(G)

theorem swap (a b : G)
  shows a * b = b * a
proof
  exact mul_comm with *
end A

theorem bridge (A m e i : Set)
  requires group : IsGroup(A, m, e, i)
  shows Group(Group.mk(A, m, e, i)) ∧ Group.carrier(Group.mk(A, m, e, i)) = A
proof
  constructor
  . exact Group.of_parts with group
  . group_projections
`);
});

test("the group is a structure: generated members, laws by their names, statements free of the projections' spellings", () => {
  const kernel = load(section(`
theorem laws (a : G)
  shows a⁻¹ * a = G.one ∧ a * a⁻¹ = G.one ∧ (a⁻¹)⁻¹ = a
proof
  have left := Group.inv_mul with *
  have right := Group.mul_inv with *
  have twice := Group.inv_involutive with *
  refine ⟨left, right, twice⟩
`));
  const basic = "Grace.Cumulus.Algebra.Group.Basic.";
  assert.equal(kernel.predicates.get(`${basic}Group`), 1);
  assert.equal(kernel.predicates.get("Grace.Cumulus.Algebra.Foundation.Algebra.IsGroup"), 4);
  for (const name of ["Group.mk.carrier", "Group.mk.mul", "Group.mk.one", "Group.mk.inv", "Group.mk.data", "Group.eta", "Group.intro", "Group.parts", "Group.of_parts"]) {
    assert.ok(kernel.theorems.has(basic + name), name);
  }
  let intro = kernel.theorems.get(`${basic}Group.intro`)!;
  const bound: string[] = [];
  while (intro.tag === "forall") { bound.push(intro.variable); intro = intro.body; }
  assert.deepEqual(bound, ["carrier", "mul", "one", "inv"]);
  let premises = 0;
  while (intro.tag === "imp") { premises += 1; intro = intro.right; }
  assert.equal(premises, 8);
  const result = check(section(`
theorem opened (a b : G)
  shows a * b * b⁻¹ = a
proof
  group_simp
`));
  const statement = result.theorems.find(item => item.name === "BundledGroups.opened")!.statement;
  assert.equal(statement, "∀ G, ∀ (a b : G), Group(G) → a * b * b⁻¹ = a");
  assert.ok(!/G\.mul|G\.inv|carrierOf|operation\(/u.test(statement));
});

test("a structure variable names its carrier where a set of elements is meant: x ∈ G, S ⊆ G, cardinality(G), Finite(G)", () => {
  const written = load(header + `
import Grace.Cumulus.Cardinal.Pigeonhole

section S
variable (G : Set)
hypothesis group : Group(G)

theorem size (S : Set)
  requires hS : S ⊆ G
  requires finite : Finite(G)
  shows cardinality(S) ≤ cardinality(G) ∧ ∀ x ∈ S, x ∈ G
proof
  constructor
  . exact cardinality.monotone with *
  . intros x hx
    exact hS with x, hx
end S
`);
  const spelled = load(header + `
import Grace.Cumulus.Cardinal.Pigeonhole

theorem size (G S : Set)
  requires group : Group(G)
  requires hS : S ⊆ G.carrier
  requires finite : Finite(G.carrier)
  shows cardinality(S) ≤ cardinality(G.carrier) ∧ ∀ x ∈ S, x ∈ G.carrier
proof
  constructor
  . exact cardinality.monotone with *
  . intros x hx
    exact hS with x, hx
`);
  assert.ok(formulaEquals(written.theorems.get("BundledGroups.size")!, spelled.theorems.get("BundledGroups.size")!));
  const result = check(header + `
import Grace.Cumulus.Cardinal.Pigeonhole

section S
variable (G : Set)
hypothesis group : Group(G)

theorem size (S : Set)
  requires hS : S ⊆ G
  requires finite : Finite(G)
  shows cardinality(S) ≤ cardinality(G) ∧ ∀ x ∈ S, x ∈ G
proof
  constructor
  . exact cardinality.monotone with *
  . intros x hx
    exact hS with x, hx
end S
`);
  const statement = result.theorems.find(item => item.name === "BundledGroups.size")!.statement;
  assert.equal(statement, "∀ G, ∀ S, Group(G) → S ⊆ G → Finite(G) → cardinality(S) ≤ cardinality(G) ∧ ∀ x ∈ S, x ∈ G");
});

const area = "lib/Grace/Cumulus/Algebra/Group/";
const groupHeader = "module BundledGroups\nimport Grace.Cumulus.Algebra.Group\n";

/** The proof lines of a theorem in a library module, excluding its header. */
function proofLines(file: string, name: string): number {
  const lines = readFileSync(area + file, "utf8").split("\n");
  const start = lines.findIndex(line => line.startsWith(`theorem ${name} `) || line === `theorem ${name}`);
  assert.ok(start >= 0, `${name} in ${file}`);
  let index = lines.indexOf("proof", start) + 1;
  let count = 0;
  while (index < lines.length && lines[index]!.trim() !== "" && lines[index]!.startsWith(" ")) { count += 1; index += 1; }
  return count;
}

test("the pilot theorems stay within their line budgets", () => {
  assert.ok(proofLines("Basic.g17", "inv_mul_cancel_left") <= 2);
  assert.ok(proofLines("Basic.g17", "Group.inv_involutive") <= 1);
  assert.ok(proofLines("Basic.g17", "inv_one") <= 3);
  assert.ok(proofLines("Basic.g17", "inv_inv") <= 4);
  assert.ok(proofLines("Subgroup.g17", "Subgroup.intersection") <= 10);
  assert.ok(proofLines("Homomorphism.g17", "GroupHom.map_inv") <= 4);
  assert.ok(proofLines("Kernel.g17", "GroupHom.kernel_subgroup") <= 10);
  const lagrange = readFileSync(area + "Lagrange.g17", "utf8");
  assert.match(lagrange, /theorem lagrange\n  requires finite : Finite\(G\)\n  shows order\(G\) = index\(G, H\) \* cardinality\(H\)/u);
  assert.match(lagrange, /theorem lagrange\.theorem\n  requires finite : Finite\(G\)\n  shows cardinality\(H\) ∣ order\(G\)/u);
  assert.match(lagrange, /theorem leftCoset\.cardinality \(g : G\)\n  requires finite : Finite\(H\)\n  shows cardinality\(g • H\) = cardinality\(H\)/u);
  const first = readFileSync(area + "FirstIsomorphism.g17", "utf8");
  assert.match(first, /theorem GroupHom\.first_isomorphism\n  requires onto : SurjectiveBetween\(f, G\.carrier, H\.carrier\)\n  shows inducedMap\(f\) : G ⧸ ker\(f\) ≃\* H/u);
});

test("a subgroup hypothesis types (h : H), supplies * and ⁻¹ on its elements, and its closure is synthesized", () => {
  const result = check(groupHeader + `
section S
variable (G H : Set)
hypothesis group : Group(G)
hypothesis subgroup : Subgroup(H, G)

theorem closed (h k : H)
  shows h * k⁻¹ ∈ H
proof
  typecheck

theorem lifted (h : H) (x : G)
  shows h⁻¹ * (h * x) = x
proof
  rw inv_mul_cancel_left
  rfl
end S
`);
  const statement = result.theorems.find(item => item.name === "BundledGroups.closed")!.statement;
  assert.equal(statement, "∀ G H, ∀ (h k : H), Group(G) → Subgroup(H, G) → h * k⁻¹ ∈ H");
});

test("f : G →* H is a transparent guard that supplies both operations, and powers are written a ^ n", () => {
  const result = check(groupHeader + `
section F
variable (f G H : Set)
hypothesis hom : f : G →* H

theorem image (a b : G)
  shows f(a * b⁻¹) = f(a) * f(b)⁻¹
proof
  exact GroupHom.map_mul_inv with *

theorem power (a : G) (n : Nat)
  shows f(a ^ (n + 1)) = f(a) ^ n * f(a)
proof
  rw [GroupHom.map_pow, pow_succ]
  rfl

theorem natural
  shows 2 ^ 3 = 8
proof
  compute
end F
`);
  const statement = result.theorems.find(item => item.name === "BundledGroups.image")!.statement;
  assert.match(statement, /GroupHom\(f, G, H\) → f\(a \* b⁻¹\) = f\(a\) \* f\(b\)⁻¹$/u);
  check(groupHeader + `
theorem image (f G H a b : Set)
  requires hom : GroupHom(f, G, H)
  requires aIn : a ∈ G.carrier
  requires bIn : b ∈ G.carrier
  shows f(call2(G.mul, a, apply(G.inv, b))) = call2(H.mul, f(a), apply(H.inv, f(b)))
proof
  exact GroupHom.map_mul_inv with *
`);
});

test("a binder typed by a variable with two carriers in scope is an error that names them", () => {
  assert.throws(() => checkWorkbenchFiles([{ name: "BundledGroups.g17", source: groupHeader + `
section S
variable (G K : Set)
hypothesis group : Group(G)
hypothesis other : Subgroup(G, K)
theorem ambiguous (a : G)
  shows a = a
proof
  rfl
end S
` }]), /ambiguous binder \(a : G\); hypotheses in scope give G the carriers G\.carrier and G/u);
});

test("G ⧸ N is the quotient group when G is a structure of a hypothesis in scope, and the set quotient otherwise", () => {
  const written = load(groupHeader + `
theorem quotient (G N : Set)
  requires group : Group(G)
  requires normal : NormalSubgroup(N, G)
  shows Group(G ⧸ N)
proof
  exact quotientGroup.group with *

theorem carrier (G N A r : Set)
  requires group : Group(G)
  shows Group.carrier(G ⧸ N) = (G.carrier ⧸ cosetRelation(G, N)) ∧ (A ⧸ r) = (A ⧸ r)
proof
  constructor
  . exact quotientGroup.carrierOf with *
  . rfl

theorem binder (G : Group) (N : Set)
  shows Group.carrier(G ⧸ N) = (G.carrier ⧸ cosetRelation(G, N))
proof
  exact quotientGroup.carrierOf with *

theorem plain (G N : Set)
  shows (G ⧸ N) = (G ⧸ N)
proof
  rfl
`, "ZFG");
  const spelled = load(groupHeader + `
theorem quotient (G N : Set)
  requires group : Group(G)
  requires normal : NormalSubgroup(N, G)
  shows Group(quotientGroup(G, N))
proof
  exact quotientGroup.group with *

theorem carrier (G N A r : Set)
  requires group : Group(G)
  shows Group.carrier(quotientGroup(G, N)) = quotient(G.carrier, cosetRelation(G, N)) ∧ quotient(A, r) = quotient(A, r)
proof
  constructor
  . exact quotientGroup.carrierOf with *
  . rfl

theorem binder (G : Group) (N : Set)
  shows Group.carrier(quotientGroup(G, N)) = quotient(G.carrier, cosetRelation(G, N))
proof
  exact quotientGroup.carrierOf with *

theorem plain (G N : Set)
  shows quotient(G, N) = quotient(G, N)
proof
  rfl
`, "ZFG");
  for (const name of ["quotient", "carrier", "binder", "plain"]) {
    assert.ok(formulaEquals(written.theorems.get(`BundledGroups.${name}`)!, spelled.theorems.get(`BundledGroups.${name}`)!), name);
  }
});

test("the quotient group prints as G ⧸ N under a group or homomorphism hypothesis, beside the set quotient", () => {
  const result = check(groupHeader + `
section S
variable (G N : Set)
hypothesis group : Group(G)
hypothesis normal : NormalSubgroup(N, G)

theorem printed (A r : Set)
  shows Group(G ⧸ N) ∧ (A ⧸ r) = (A ⧸ r)
proof
  constructor
  . exact quotientGroup.group with *
  . rfl
end S

section T
variable (f G H : Set)
hypothesis hom : f : G →* H

theorem descended
  requires onto : SurjectiveBetween(f, G.carrier, H.carrier)
  shows G ⧸ ker(f) ≃* H
proof
  exact GroupHom.quotient_isomorphic with *

theorem induced
  requires onto : SurjectiveBetween(f, G.carrier, H.carrier)
  shows inducedMap(f) : G ⧸ ker(f) ≃* H
proof
  exact GroupHom.first_isomorphism with *
end T
`);
  const printed = result.theorems.find(item => item.name === "BundledGroups.printed")!.statement;
  assert.match(printed, /Group\(G ⧸ N\) ∧ \(A ⧸ r\) = \(A ⧸ r\)$/u);
  const descended = result.theorems.find(item => item.name === "BundledGroups.descended")!.statement;
  assert.match(descended, /→ G ⧸ ker\(f\) ≃\* H$/u);
  const induced = result.theorems.find(item => item.name === "BundledGroups.induced")!.statement;
  assert.match(induced, /→ GroupIso\(inducedMap\(f\), G ⧸ ker\(f\), H\)$/u);
});

test("rw? ranks a rule that closes the goal first and never offers a rule whose pattern is a bare variable", () => {
  const kernel = load(section(`
theorem unit_square
  shows G.one = G.one * G.one
proof
  rw?
  rfl
`));
  const trace = kernel.theoremTacticTraces.get("BundledGroups.unit_square")!;
  const items = trace.steps[0]!.info!.items;
  // Both unit laws close the goal; they come first, in either order.
  assert.deepEqual(items.slice(0, 2).sort(), ["rw mul_one", "rw one_mul"]);
  assert.ok(!items.some(item => /union\.singleton|intersection\.idempotent|union2\.idempotent/u.test(item)), items.join("; "));
});

test("an unknown settle rule names the nearest declared one", () => {
  assert.throws(() => load(section(`
theorem unit_square
  shows G.one * G.one = G.one
proof
  simp [mul.right_one]
`)), /unknown settle rule mul\.right_one; did you mean mul_one\?/u);
});
