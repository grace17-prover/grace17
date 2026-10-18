// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The `structure` declaration: a one-constructor datatype with named
// fields, generated projections with their laws, eta, the predicate that
// conjoins the shape, the field typing, and the `where` laws, and the
// introduction theorem; dot notation `C.obj` parses from a hypothesis in
// scope or an unambiguous field and prints back; ambiguity is an error
// naming the qualified spellings; parameters index the predicate.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, instanceReport, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module Structures\nimport Grace.Cumulus.Set.Function\n";

const pointed = `
structure Pointed
  | carrier : Set
  | point : Set
  where
    member : point ∈ carrier
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Structures.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "Structures.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name === name)!.statement;

test("a structure is a one-constructor datatype with projections, projection laws, shape, eta, and intro", () => {
  const kernel = load(header + pointed);
  const datatype = kernel.datatypes.get("Structures.Pointed.inductive")!;
  assert.equal(datatype.predicate, "Structures.Pointed.Data");
  assert.deepEqual(datatype.constructors.map(item => [item.name, item.arity]), [["Structures.Pointed.mk", 2]]);
  assert.equal(datatype.setTheoreticEncoding, true);
  const declaration = kernel.definitions.get("Structures.Pointed.inductive")!;
  for (const property of ["representation.mk", "constructor.mk", "injective.mk", "cases"]) assert.ok(declaration.properties.has(property));
  assert.equal(kernel.definitions.get("Structures.Pointed.carrier")!.kind, "recursive");
  assert.equal(kernel.predicates.get("Structures.Pointed"), 1);
  for (const name of ["Pointed.mk.carrier", "Pointed.mk.point", "Pointed.mk.data", "Pointed.eta", "Pointed.intro"]) {
    assert.ok(kernel.theorems.has(`Structures.${name}`), name);
  }
  const result = check(header + pointed);
  assert.equal(statement(result, "Structures.Pointed.mk.carrier"), "∀ carrier, ∀ point, Pointed.carrier(Pointed.mk(carrier, point)) = carrier");
  assert.equal(statement(result, "Structures.Pointed.mk.data"), "∀ carrier, ∀ point, Pointed.Data(Pointed.mk(carrier, point))");
  assert.equal(statement(result, "Structures.Pointed.eta"), "∀ self, Pointed.Data(self) → self = Pointed.mk(self.carrier, self.point)");
  assert.equal(statement(result, "Structures.Pointed.intro"), "∀ carrier, ∀ point ∈ carrier, Pointed(Pointed.mk(carrier, point))");
});

test("the predicate conjoins the shape and the laws at the projections, and the generated theorems are usable", () => {
  check(header + pointed + `
theorem projections (A x : Set)
  shows Pointed.carrier(Pointed.mk(A, x)) = A ∧ Pointed.point(Pointed.mk(A, x)) = x
proof
  constructor
  . exact Pointed.mk.carrier at A, x
  . exact Pointed.mk.point at A, x

theorem laws (P : Set)
  requires pointed : Pointed(P)
  shows Pointed.Data(P) ∧ P.point ∈ P.carrier ∧ P = Pointed.mk(P.carrier, P.point)
proof
  obtain ⟨shape, member⟩ := pointed
  have eta := Pointed.eta with shape
  refine ⟨shape, member, eta⟩

theorem intro (A x : Set)
  requires xIn : x ∈ A
  shows Pointed(Pointed.mk(A, x))
proof
  exact Pointed.intro with xIn

theorem computed
  shows Pointed.point(Pointed.mk(∅, ∅)) = ∅
proof
  compute
`);
});

test("soft-typed fields become typing conjuncts, and a field typed by a structure is a nested structure", () => {
  const result = check(header + pointed + `
structure Magma
  | (carrier : Set) (op : carrier × carrier → carrier)

structure Based
  | (base : Pointed) (extra : Set)

theorem magma (A f : Set)
  requires fFunction : f : A × A → A
  shows Magma(Magma.mk(A, f))
proof
  exact Magma.intro with fFunction

theorem nested (B : Set)
  requires based : Based(B)
  shows B.base.point ∈ B.base.carrier
proof
  obtain ⟨shape, pointedShape, member⟩ := based
  exact member
`);
  assert.equal(statement(result, "Structures.Magma.intro"), "∀ carrier, ∀ (op : carrier × carrier → carrier), Magma(Magma.mk(carrier, op))");
  assert.equal(statement(result, "Structures.nested"), "∀ B, Based(B) → B.base.point ∈ B.base.carrier");
});

test("a field typed by an earlier field is a member of it, and the typing conjunct is usable", () => {
  const result = check(header + `
structure Based
  | carrier : Set
  | point : carrier
  | op : carrier × carrier → carrier

theorem based (B : Set)
  requires based : Based(B)
  shows B.point ∈ B.carrier ∧ (B.op : B.carrier × B.carrier → B.carrier)
proof
  obtain ⟨shape, member, operation⟩ := based
  exact ⟨member, operation⟩
`);
  assert.equal(statement(result, "Structures.Based.intro"),
    "∀ carrier, ∀ point ∈ carrier, ∀ (op : carrier × carrier → carrier), Based(Based.mk(carrier, point, op))");
  assert.equal(statement(result, "Structures.based"), "∀ B, Based(B) → B.point ∈ B.carrier ∧ FunctionBetween(B.op, B.carrier × B.carrier, B.carrier)");
});

test("C.obj parses from the hypothesis in scope or an unambiguous field, obj(C) stays accepted, and both print as C.obj", () => {
  const source = header + pointed + `
structure Flagged
  | point : Set
  | flag : Set

theorem dotted (P : Set)
  requires pointed : Pointed(P)
  shows P.point ∈ P.carrier
proof
  obtain ⟨shape, member⟩ := pointed
  exact member

theorem applied (P f : Set)
  requires pointed : Pointed(P)
  shows P.point(f) = point(P)(f) ∧ P.carrier(f, f) = carrier(P)(f, f)
proof
  constructor
  . rfl
  . rfl

theorem flagged (Q : Set)
  requires flagged : Flagged(Q)
  shows Q.point = Flagged.point(Q)
proof
  rfl

theorem constructed (A x : Set)
  shows point(Pointed.mk(A, x)) = x
proof
  exact Pointed.mk.point at A, x
`;
  const result = check(source);
  assert.equal(statement(result, "Structures.dotted"), "∀ P, Pointed(P) → P.point ∈ P.carrier");
  assert.equal(statement(result, "Structures.applied"), "∀ P, ∀ f, Pointed(P) → P.point(f) = P.point(f) ∧ P.carrier(f, f) = P.carrier(f, f)");
  assert.equal(statement(result, "Structures.flagged"), "∀ Q, Flagged(Q) → Q.point = Q.point");
  assert.equal(statement(result, "Structures.constructed"), "∀ A, ∀ x, Pointed.point(Pointed.mk(A, x)) = x");
  const spelled = load(source.replace("shows P.point ∈ P.carrier", "shows Pointed.point(P) ∈ Pointed.carrier(P)"));
  assert.ok(formulaEquals(load(source).theorems.get("Structures.dotted")!, spelled.theorems.get("Structures.dotted")!));
});

test("a receiver already used as a structure by a fact in scope resolves, and an ambiguous projection is an error naming the spellings", () => {
  check(header + pointed + `
structure Flagged
  | point : Set
  | flag : Set

predicate Centered (P x : Set) := x ∈ Pointed.carrier(P) ∧ x = Pointed.point(P)

theorem used (P x : Set)
  requires centered : Centered(P, x)
  shows x ∈ P.carrier ∧ point(P) = x
proof
  obtain ⟨xIn, same⟩ := centered
  constructor
  . exact xIn
  . symm
    exact same
`);
  assert.throws(() => load(header + pointed + `
structure Flagged
  | point : Set
  | flag : Set

theorem loose (P : Set)
  shows P.point = P.point
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError &&
    /ambiguous projection point of P.*Pointed\.point\(P\) or Flagged\.point\(P\)/u.test(error.message));
  assert.throws(() => load(header + pointed + `
theorem missing (P : Set)
  shows P.colour = P.colour
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError && /colour is not a field of any structure/u.test(error.message));
});

test("structure parameters index the predicate after the value, and earlier laws supply the notation of later ones", () => {
  const result = check(header + `
import Grace.Cumulus.Category.Core

structure Tagged (T : Set)
  | tag payload : Set
  where
    same : tag = T
    member : payload ∈ tag

theorem tagged (T x : Set)
  requires xIn : x ∈ T
  shows Tagged(Tagged.mk(T, x), T)
proof
  apply Tagged.intro
  . rfl
  . exact xIn

structure Endomorphism (C : Set)
  | object arrow : Set
  where
    category : Category(C)
    object_in : object ∈ C.obj
    typed : arrow : object ⟶ object
`);
  assert.equal(statement(result, "Structures.tagged"), "∀ T, ∀ x ∈ T, Tagged(Tagged.mk(T, x), T)");
  assert.equal(statement(result, "Structures.Endomorphism.intro"),
    "∀ C, ∀ object, ∀ arrow, Category(C) → object ∈ C.obj → Morphism(C, arrow, object, object) → Endomorphism(Endomorphism.mk(object, arrow), C)");
});

test("malformed declarations are rejected with their line", () => {
  for (const [body, message] of [
    ["structure Empty\n", /needs a field line/u],
    ["structure Bad\n  | x : Set\n  where\n    law : x ∈ x\n    law : x = x\n", /distinct names/u],
    ["structure Shadow\n  | obj : Set\n  where\n    law : ∀ obj, obj = obj\n", /binds obj/u],
    ["structure Self\n  | self : Set\n", /self/u],
  ] as const) {
    assert.throws(() => load(header + body), (error: unknown) => error instanceof SurfaceError && message.test(error.message), body);
  }
});

// `extends`: the fields of the parents become fields of the child, sharing
// the carrier; each parent is a value `C.base` built by the parent's
// constructor from the child's fields; the parent predicate at that value
// is a law of the child and an instance; parent fields are renamed or fixed
// with `(mul := add, inv := ∅)`; the hypothesis notation of a parent whose
// fields keep their names is inherited; a soft-typed parameter is a typing
// conjunct.

const magma = `
structure Magma
  | carrier : Set
  | op : carrier × carrier → carrier

notation infixl 70 "⋆" => call2(M.op, _, _) via hypothesis Magma(M) for M.carrier
`;

test("a structure extends a parent: inherited fields, the parent as a value, its laws, and its instance", () => {
  const source = header + pointed + `
structure Marked extends Pointed as base
  | mark : Set
  where
    marked : mark ∈ carrier

theorem opened (M : Set)
  requires marked : Marked(M)
  shows M.base.point ∈ M.carrier ∧ M.mark ∈ M.carrier
proof
  obtain ⟨shape, base, markIn⟩ := marked
  obtain ⟨baseShape, member⟩ := base
  rw Marked.base.carrier at member
  exact ⟨member, markIn⟩

theorem built (A x y : Set)
  requires xIn : x ∈ A
  requires yIn : y ∈ A
  shows Marked(Marked.mk(A, x, y))
proof
  have pointed := Pointed.intro with xIn
  exact Marked.intro with pointed, yIn

theorem instance_found (M : Set)
  requires marked : Marked(M)
  shows Pointed(M.base)
proof
  exact Marked.base.pointed with *

theorem projected (M : Set)
  requires marked : Marked(M)
  shows M.base.point = M.point ∧ M.base = Pointed.mk(M.carrier, M.point)
proof
  constructor
  . exact Marked.base.point at M
  . exact Marked.base.value at M
`;
  const result = check(source);
  const kernel = load(source);
  assert.deepEqual(kernel.datatypes.get("Structures.Marked.inductive")!.constructors.map(item => [item.name, item.arity]),
    [["Structures.Marked.mk", 3]]);
  assert.ok(kernel.definitions.has("Structures.Marked.base"));
  assert.equal(statement(result, "Structures.Marked.base.value"),
    "∀ self, self.base = Pointed.mk(self.carrier, self.point)");
  assert.equal(statement(result, "Structures.Marked.base.carrier"), "∀ self, self.base.carrier = self.carrier");
  assert.equal(statement(result, "Structures.Marked.base.point"), "∀ self, self.base.point = self.point");
  assert.equal(statement(result, "Structures.Marked.mk.base"),
    "∀ carrier, ∀ point, ∀ mark, Marked.base(Marked.mk(carrier, point, mark)) = Pointed.mk(carrier, point)");
  assert.equal(statement(result, "Structures.Marked.intro"),
    "∀ carrier, ∀ point, ∀ mark, Pointed(Pointed.mk(carrier, point)) → mark ∈ carrier → Marked(Marked.mk(carrier, point, mark))");
  assert.equal(statement(result, "Structures.Marked.base.pointed"), "∀ self, Marked(self) → Pointed(self.base)");
  assert.equal(statement(result, "Structures.Marked.base.mem"),
    "∀ self, ∀ x ∈ self.carrier, x ∈ self.base.carrier");
  assert.ok(instanceReport(kernel).some(item => item.name === "Structures.Marked.base.pointed"));
  const unfolded = load(source.replace("shows M.base.point ∈ M.carrier ∧ M.mark ∈ M.carrier",
    "shows Pointed.point(Marked.base(M)) ∈ Marked.carrier(M) ∧ Marked.mark(M) ∈ Marked.carrier(M)"));
  assert.ok(formulaEquals(kernel.theorems.get("Structures.opened")!, unfolded.theorems.get("Structures.opened")!));
});

test("parent fields are renamed or fixed, parents share the carrier, and the notation of an unrenamed parent is inherited", () => {
  const source = header + pointed + magma + `
structure Twin extends Magma as left (op := plus), Magma as right (op := times)
  where
    absorbs : ∀ x y ∈ carrier, times(x, plus(x, y)) = x

structure Flat extends Pointed as base (point := ∅)

structure UnitalMagma extends Magma as magma
  | unit : carrier
  where
    left_unit : ∀ x ∈ carrier, op(unit, x) = x

theorem unital (U : Set)
  requires unital : UnitalMagma(U)
  shows ∀ x ∈ U, U.unit ⋆ x = x
proof
  obtain ⟨shape, opF, unitIn, magma, leftUnit⟩ := unital
  exact leftUnit

section Unital
variable (U : Set)
hypothesis unital : UnitalMagma(U)

theorem inherited (x : U)
  shows U.unit ⋆ x ∈ U
proof
  obtain ⟨shape, opF, unitIn, magma, leftUnit⟩ := unital
  have equal := leftUnit with x, *
  rw equal
  assumption
end Unital

theorem flat (F : Set)
  requires flat : Flat(F)
  shows F.base.point = ∅
proof
  exact Flat.base.point at F
`;
  const result = check(source);
  assert.equal(statement(result, "Structures.Twin.intro"),
    "∀ carrier, ∀ (plus times : carrier × carrier → carrier), " +
    "Magma(Magma.mk(carrier, plus)) → Magma(Magma.mk(carrier, times)) → (∀ x ∈ carrier, ∀ y ∈ carrier, times(x, plus(x, y)) = x) → " +
    "Twin(Twin.mk(carrier, plus, times))");
  assert.equal(statement(result, "Structures.Twin.right.op"), "∀ self, self.right.op = self.times");
  assert.equal(statement(result, "Structures.Flat.intro"), "∀ carrier, Pointed(Pointed.mk(carrier, ∅)) → Flat(Flat.mk(carrier))");
  assert.equal(statement(result, "Structures.Flat.base.point"), "∀ self, self.base.point = ∅");
  assert.equal(statement(result, "Structures.unital"), "∀ U, UnitalMagma(U) → ∀ x ∈ U.carrier, U.unit ⋆ x = x");
  assert.equal(statement(result, "Structures.inherited"), "∀ U, ∀ (x : U), UnitalMagma(U) → U.unit ⋆ x ∈ U");
  const spelled = load(source.replace("shows ∀ x ∈ U, U.unit ⋆ x = x",
    "shows ∀ x ∈ UnitalMagma.carrier(U), call2(UnitalMagma.op(U), UnitalMagma.unit(U), x) = x"));
  assert.ok(formulaEquals(load(source).theorems.get("Structures.unital")!, spelled.theorems.get("Structures.unital")!));
  // A renamed operation carries no inherited token: Twin(T) supplies no ⋆.
  assert.throws(() => load(header + pointed + magma + `
structure Twin extends Magma as left (op := plus), Magma as right (op := times)

theorem loose (T x y : Set)
  requires twin : Twin(T)
  requires xIn : x ∈ T.carrier
  requires yIn : y ∈ T.carrier
  shows x ⋆ y = x ⋆ y
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError && /no hypothesis in scope supplies an operation for ⋆/u.test(error.message));
});

test("a predicate over a structure is a parent, and projections of the parent value resolve through its structure", () => {
  const source = header + pointed + `
predicate Settled (P : Set) := Pointed(P) ∧ (∃ x, x ∈ P.carrier)

structure Rich extends Settled as base
  | extra : Set

theorem rich (R : Set)
  requires rich : Rich(R)
  shows Settled(R.base) ∧ R.base.point = R.point
proof
  obtain ⟨shape, base⟩ := rich
  constructor
  . exact base
  . exact Rich.base.point at R
`;
  const result = check(source);
  assert.equal(statement(result, "Structures.Rich.base.settled"), "∀ self, Rich(self) → Settled(self.base)");
  assert.equal(statement(result, "Structures.Rich.intro"),
    "∀ carrier, ∀ point, ∀ extra, Settled(Pointed.mk(carrier, point)) → Rich(Rich.mk(carrier, point, extra))");
});

test("a soft-typed structure parameter is a typing conjunct before the fields", () => {
  const result = check(header + pointed + `
structure Over (P : Pointed)
  | item : Set
  where
    item_in : item ∈ P.carrier

theorem over (P x : Set)
  requires over : Over(x, P)
  shows Pointed(P) ∧ x.item ∈ P.carrier
proof
  obtain ⟨shape, pointed, itemIn⟩ := over
  exact ⟨pointed, itemIn⟩
`);
  assert.equal(statement(result, "Structures.Over.intro"),
    "∀ P, ∀ item, Pointed(P) → item ∈ P.carrier → Over(Over.mk(item), P)");
});

test("malformed extends clauses are rejected with their line", () => {
  for (const [body, message] of [
    ["structure Bad extends Missing as base\n  | x : Set\n", /unknown parent Missing/u],
    ["structure Bad extends Pointed\n  | x : Set\n", /as base/u],
    ["structure Bad extends Pointed as base, Pointed as base\n", /distinct/u],
    ["structure Bad extends Pointed as point\n", /distinct/u],
    ["structure Bad extends Pointed as base\n  | point : Set\n", /already a field/u],
    ["structure Bad extends Pointed as base (colour := red)\n", /colour is not a field of Pointed/u],
  ] as const) {
    assert.throws(() => load(header + pointed + body), (error: unknown) => error instanceof SurfaceError && message.test(error.message), body);
  }
});
