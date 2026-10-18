// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";
const prefix = `module Guards
namespace Guards
import Grace.Core.List

theorem natural (n : Nat)
  shows n = n
proof
  rfl

theorem list (A : Set) (xs : List(A))
  shows xs = xs
proof
  rfl
`;
function load(body: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Guards.g17", source: prefix + body + "\nend Guards\n" }], ["lib"]);
  return kernel;
}

test("guarded inference emits the same proof as explicit instantiation", () => {
  const body = (application: string) => `theorem application (A : Set) (xs : List(A))
  shows xs = xs
proof
  exact ${application}
`;
  const inferred = load(body("list with *"));
  const explicit = load(body("list at A, xs with *"));
  const a = compileProofModule([exportTheoremForMachine(inferred, "Guards.application")]);
  const b = compileProofModule([exportTheoremForMachine(explicit, "Guards.application")]);
  assert.deepEqual(a, b);
  verifyProofMachine(inferred, a);
});

test("inference can reconstruct a natural guard but cannot invent it", () => {
  const good = load(`theorem good
  shows zero = zero
proof
  exact natural with *
`);
  verifyProofMachine(good, compileProofModule([exportTheoremForMachine(good, "Guards.good")]));
  assert.throws(() => load(`theorem bad (x : Set)
  shows x = x
proof
  exact natural with *
`), /cannot find evidence for [a-z]+ : ℕ/);
});

test("ambiguous dependent carriers require explicit arguments", () => {
  assert.throws(() => load(`theorem bad (A B xs : Set)
  requires first : List(A, xs)
  requires second : List(B, xs)
  shows xs = xs
proof
  exact list with *
`), /cannot uniquely infer parameters A/);
});

test("a missing dependent list guard cannot be inferred from a reflexive conclusion", () => {
  assert.throws(() => load(`theorem bad (A xs : Set)
  shows xs = xs
proof
  exact list with *
`), /cannot uniquely infer parameters A/);
});

test("typed guards do not consume an implication inside the theorem conclusion", () => {
  const kernel = load(`theorem implication (n : Nat)
  shows n = n → n = n
proof
  intro h
  exact h

theorem application (n : Nat)
  shows n = n → n = n
proof
  exact implication with *
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("annotated local facts infer guarded parameters and preserve explicit certificates", () => {
  const body = (application: string) => `theorem application (A : Set) (xs : List(A))
  shows xs = xs
proof
  have result : xs = xs := ${application}
  exact result
`;
  const inferred = load(body("list with *"));
  const explicit = load(body("list at A, xs with *"));
  const a = compileProofModule([exportTheoremForMachine(inferred, "Guards.application")]);
  const b = compileProofModule([exportTheoremForMachine(explicit, "Guards.application")]);
  assert.deepEqual(a, b);
  verifyProofMachine(inferred, a);
});

test("local annotations are checked even when the resulting fact is unused", () => {
  assert.throws(() => load(`theorem bad (x y : Set)
  requires hx : x = x
  shows x = x
proof
  have falseFact : x = y := hx
  exact hx
`), /local proof falseFact states .*but its proof establishes/);
});

test("a local annotation neither supplies evidence nor chooses an ambiguous carrier", () => {
  assert.throws(() => load(`theorem bad (x : Set)
  shows x = x
proof
  have result : x = x := natural with *
  exact result
`), /cannot find evidence for [a-z]+ : ℕ/);
  assert.throws(() => load(`theorem bad (A B xs : Set)
  requires first : List(A, xs)
  requires second : List(B, xs)
  shows xs = xs
proof
  have result : xs = xs := list with *
  exact result
`), /cannot uniquely infer parameters A/);
});

test("local annotations guide inference independently of the enclosing goal", () => {
  const kernel = load(`theorem application (m n : Nat)
  shows m = m ∧ n = n
proof
  have left : m = m := natural with *
  have right : n = n := natural with *
  refine ⟨left, right⟩
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("annotated facts preserve goal history on cached checks and reject a changed annotation", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  const source = prefix + `theorem application (n : Nat)
  shows n = n
proof
  have result : n = n := natural with *
  exact result
end Guards
`;
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "Guards.g17", source }], "ZF", ["Guards.g17"]);
    const theorem = result.theorems.find(t => t.name === "Guards.application");
    assert.ok(theorem);
    assert.match(JSON.stringify(theorem.steps), /have result/);
  }
  assert.throws(() => checkWorkbenchFiles([{ name: "Guards.g17", source: source.replace("have result : n = n", "have result : n = 0") }], "ZF", ["Guards.g17"]));
});

test("browser and native elaborators agree on annotated local facts", async () => {
  const native = await import("../src/workbench.ts");
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = prefix + `theorem application (A : Set) (xs : List(A))
  shows xs = xs
proof
  have result : xs = xs := list with *
  exact result
end Guards
`;
  const files = [{ name: "Guards.g17", source }];
  const a = native.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
  const b = browser.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
  assert.equal(b.ok, true);
  assert.equal(b.digest, a.digest);
  assert.deepEqual(b.theorems.map(t => t.statement), a.theorems.map(t => t.statement));
});

const equivalence = `theorem duplicate (n : Nat)
  shows n = n ↔ n = n ∧ n = n
proof
  tauto
`;

test("both equivalence directions infer parameters and retain explicit certificates", () => {
  for (const direction of ["forward", "backward"]) {
    const forward = direction === "forward";
    const premise = forward ? "n = n" : "n = n ∧ n = n";
    const goal = forward ? "n = n ∧ n = n" : "n = n";
    const body = (args: string) => equivalence + `theorem application (n : Nat)
  requires evidence : ${premise}
  shows ${goal}
proof
  have result : ${goal} := duplicate.${direction}${args} with *
  exact result
`;
    const inferred = load(body(""));
    const explicit = load(body(" at n"));
    const a = compileProofModule([exportTheoremForMachine(inferred, "Guards.application")]);
    const b = compileProofModule([exportTheoremForMachine(explicit, "Guards.application")]);
    assert.deepEqual(a, b);
    verifyProofMachine(inferred, a);
  }
});

test("direction inference cannot invent the selected antecedent", () => {
  assert.throws(() => load(equivalence + `theorem bad (n : Nat)
  shows n = n ∧ n = n
proof
  exact duplicate.forward with *
`), /cannot find evidence/);
});

test("direction inference preserves implications in the selected conclusion", () => {
  const kernel = load(`theorem negative (n : Nat)
  shows (n = n → ⊥) ↔ (n = n → ⊥)
proof
  tauto

theorem application (n : Nat)
  requires negative : n = n → ⊥
  requires diagonal : n = n
  shows n = n → ⊥
proof
  exact Guards.negative.forward with *
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("selected antecedents can infer parameters absent from the conclusion", () => {
  const bridge = `theorem drop (x y : Set)
  requires diagonal : x = x
  shows (x = x ∧ y = y) ↔ y = y
proof
  tauto
`;
  const kernel = load(bridge + `theorem application (a b : Set)
  requires diagonal : a = a
  requires pair : a = a ∧ b = b
  shows b = b
proof
  exact drop.forward with *
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
  assert.throws(() => load(bridge + `theorem ambiguous (a b c : Set)
  requires first : a = a
  requires second : c = c
  requires left : a = a ∧ b = b
  requires right : c = c ∧ b = b
  shows b = b
proof
  exact drop.forward with *
`), /cannot uniquely infer parameters x/);
});

test("direction inference rejects a non-equivalence before applying premises", () => {
  assert.throws(() => load(`theorem bad (n : Nat)
  shows n = n
proof
  exact natural.forward with *
`), /not an equivalence/);
});

test("browser and native inference agree on selected equivalence directions", async () => {
  const native = await import("../src/workbench.ts");
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = prefix + equivalence + `theorem application (n : Nat)
  requires diagonal : n = n
  shows n = n ∧ n = n
proof
  exact duplicate.forward with *
end Guards
`;
  const files = [{ name: "Guards.g17", source }];
  const a = native.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
  for (let i = 0; i < 2; i++) {
    const b = browser.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
    assert.equal(b.ok, true);
    assert.equal(b.digest, a.digest);
    assert.deepEqual(b.theorems.map(t => t.statement), a.theorems.map(t => t.statement));
    assert.match(JSON.stringify(b.theorems.at(-1)?.steps), /duplicate.forward/);
  }
});

test("refine components and calc steps use their own expected propositions", () => {
  for (const shape of ["refine", "calc"]) {
    const body = (args: string) => `theorem application (m n : Nat)
  shows ${shape === "refine" ? "m = m ∧ n = n" : "m = m"}
proof
${shape === "refine" ? `  refine ⟨natural${args ? " at m" : ""} with *, natural${args ? " at n" : ""} with *⟩` : `  calc\n    m = m := natural${args ? " at m" : ""} with *`}
`;
    const inferred = load(body(""));
    const explicit = load(body("explicit"));
    const a = compileProofModule([exportTheoremForMachine(inferred, "Guards.application")]);
    const b = compileProofModule([exportTheoremForMachine(explicit, "Guards.application")]);
    assert.deepEqual(a, b);
    verifyProofMachine(inferred, a);
  }
});

test("refine can infer a complete conjunction component", () => {
  const kernel = load(equivalence + `theorem application (n : Nat)
  requires diagonal : n = n
  shows n = n ∧ (n = n ∧ n = n)
proof
  refine ⟨diagonal, duplicate.forward with *⟩
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("refine inference never manufactures carrier evidence", () => {
  assert.throws(() => load(`theorem bad (m : Nat) (x : Set)
  shows m = m ∧ x = x
proof
  refine ⟨natural with *, natural with *⟩
`), /cannot find evidence for [a-z]+ : ℕ/);
});

test("a final existential proof application infers from that component", () => {
  const kernel = load(`theorem witness (n : Nat)
  shows ∃ x, x = n
proof
  refine ⟨n, rfl⟩

theorem application (n : Nat)
  shows n = n ∧ (∃ x, x = n)
proof
  refine ⟨natural with *, witness with *⟩
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("browser and native constructors use the same component inference", async () => {
  const native = await import("../src/workbench.ts");
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = prefix + `theorem application (m n : Nat)
  shows m = m ∧ n = n
proof
  refine ⟨natural with *, natural with *⟩
end Guards
`;
  const files = [{ name: "Guards.g17", source }];
  const a = native.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
  for (let i = 0; i < 2; i++) {
    const b = browser.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
    assert.equal(b.ok, true);
    assert.equal(b.digest, a.digest);
    assert.deepEqual(b.theorems.map(t => t.statement), a.theorems.map(t => t.statement));
    assert.match(JSON.stringify(b.theorems.at(-1)?.steps), /refine/);
  }
});

test("calc inference uses an intermediate step rather than the enclosing equality", () => {
  const kernel = load(`theorem application (m n : Nat)
  requires equal : m = n
  shows m = n
proof
  calc
    m = m := natural with *
    _ = n := equal
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("bare apply infers parameters and leaves declared requirements as subgoals", () => {
  const body = (args: string) => `theorem expand (n : Nat)
  requires diagonal : n = n
  shows n = n ∧ n = n
proof
  refine ⟨diagonal, diagonal⟩

theorem application (n : Nat)
  shows n = n ∧ n = n
proof
  apply expand${args}
  rfl
`;
  const inferred = load(body(""));
  const explicit = load(body(" at n with *{1}"));
  const a = compileProofModule([exportTheoremForMachine(inferred, "Guards.application")]);
  const b = compileProofModule([exportTheoremForMachine(explicit, "Guards.application")]);
  assert.deepEqual(a, b);
  verifyProofMachine(inferred, a);
  const trace = inferred.theoremTacticTraces.get("Guards.application")!;
  assert.equal(trace.steps[0]!.after.goals.length, 1);
  assert.equal(trace.steps[0]!.after.goals[0]!.goal.tag, "eq");
});

test("apply directions preserve open requirements and the selected antecedent", () => {
  const kernel = load(`theorem guarded (n : Nat)
  requires needed : n = n
  shows n = n ↔ n = n ∧ n = n
proof
  tauto

theorem application (n : Nat)
  shows n = n ∧ n = n
proof
  apply guarded.forward
  . rfl
  . rfl
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
  assert.equal(kernel.theoremTacticTraces.get("Guards.application")!.steps[0]!.after.goals.length, 2);
});

test("apply preserves a conclusion which is itself an implication", () => {
  const kernel = load(`theorem conditional (n : Nat)
  requires needed : n = n
  shows n = n → n = n
proof
  intro h
  exact h

theorem application (n : Nat)
  shows n = n → n = n
proof
  apply conditional
  rfl
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
  assert.equal(kernel.theoremTacticTraces.get("Guards.application")!.steps[0]!.after.goals.length, 1);
});

test("apply leaves missing carrier evidence as an obligation and refuses ambiguity", () => {
  assert.throws(() => load(`theorem bad (x : Set)
  shows x = x
proof
  apply natural
`));
  assert.throws(() => load(`theorem bad (A B xs : Set)
  requires first : List(A, xs)
  requires second : List(B, xs)
  shows xs = xs
proof
  apply list
`), /cannot uniquely infer parameters A/);
});

test("browser and native apply agree on residual goals and cached histories", async () => {
  const native = await import("../src/workbench.ts");
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = prefix + equivalence + `theorem application (n : Nat)
  shows n = n ∧ n = n
proof
  apply duplicate.forward
  rfl
end Guards
`;
  const files = [{ name: "Guards.g17", source }];
  const a = native.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
  for (let i = 0; i < 2; i++) {
    const b = browser.checkWorkbenchFiles(files, "ZF", ["Guards.g17"]);
    assert.equal(b.ok, true);
    assert.equal(b.digest, a.digest);
    const theorem = b.theorems.find(t => t.name === "Guards.application")!;
    assert.equal(theorem.steps[0]!.after.goals.length, 1);
    assert.equal(theorem.steps.at(-1)!.after.goals.length, 0);
  }
});

test("apply accepts an already matching local implication", () => {
  const kernel = load(`theorem application (x : Set)
  requires given : x = x → x = x
  shows x = x → x = x
proof
  apply given
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

// Carrier guards of an explicit apply are routine: they are discharged
// from the context, and only the mathematical requirement remains a goal.
test("explicit apply discharges carrier subgoals and keeps the requirement", () => {
  const kernel = load(`theorem guarded (b : Set) (a : Nat)
  requires other : b = b
  shows a = a
proof
  rfl

theorem application (m n : Nat)
  shows n = n
proof
  apply guarded at m, n
  rfl
`);
  const trace = kernel.theoremTacticTraces.get("Guards.application")!;
  assert.equal(trace.steps[0]!.after.goals.length, 1);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});

test("named implicit assignments inside local propositions are not proof assignments", () => {
  const kernel = load(`theorem application (A : Set)
  shows ListOps.length{A := A}(List.nil) = 0
proof
  have block : ListOps.length{A := A}(List.nil) = 0
    exact length.nil at A
  have inline : ListOps.length{A := A}(List.nil) = 0 := block
  exact inline
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Guards.application")]));
});
