// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Round five of the surface syntax polish, from the cycle double cover
// proofs: a theorem header's binder list wraps onto indented lines; `set x
// := t with h` names a term; membership in a natural number, and in ℕ, is
// naturality for every guard; a fact proved before `induction n` stays in
// the cases; and a forward reference names the later line.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod, scanSearchDeclarations } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[]; readonly theorems?: readonly string[] }

const header = `module SyntaxRoundFive
import Grace.Cumulus.Nat.Foundation

`;

function check(source: string): CheckResult {
  return callMachineMethod("check", { files: [{ name: "SyntaxRoundFive.g17", source: header + source }] }) as CheckResult;
}

function checks(source: string): CheckResult {
  const result = check(source);
  assert.equal(result.status, "checked", result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
  return result;
}

function failure(source: string): string {
  const result = check(source);
  assert.equal(result.status, "failed", "the module should not check");
  return result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n");
}

const wrapped = `
theorem wrappedHeader (A B : Set,
    k : Nat) (C : Set)
  requires sub : A ⊆ B
  shows A ⊆ B
proof
  exact sub

theorem wrappedBeforeParen (A B : Set
  )
  shows A ⊆ A
proof
  intros x hx
  exact hx
`;

test("a theorem header's binder list continues onto more-indented lines", () => {
  checks(wrapped);
  const source = header + wrapped;
  const result = callMachineMethod("signature", {
    name: "wrappedHeader", files: [{ name: "SyntaxRoundFive.g17", source }],
  }) as { signature: string; parameters: readonly { name: string }[] };
  assert.match(result.signature, /^theorem wrappedHeader \(A B : Set, k : Nat\) \(C : Set\)\n/u);
  assert.deepEqual(result.parameters.map(item => item.name), ["A", "B", "k", "C"]);
  const scanned = scanSearchDeclarations("SyntaxRoundFive.g17", source);
  assert.equal(scanned.find(item => item.short === "wrappedBeforeParen")?.signature.split("\n")[0], "theorem wrappedBeforeParen (A B : Set )");
  const checked = callMachineMethod("check", { files: [{ name: "SyntaxRoundFive.g17", source }] }) as { checked?: readonly { theorems: readonly string[] }[]; theorems?: readonly { name: string }[] };
  const names = JSON.stringify(checked);
  assert.match(names, /wrappedHeader/u);
  assert.match(names, /wrappedBeforeParen/u);
});

test("set x := t with h names a term in the goal and keeps the equation", () => {
  checks(`
theorem named (A B : Set)
  requires sub : A ⊆ B
  shows A ∩ B ⊆ B ∪ (A ∩ B)
proof
  set C := A ∩ B with hC
  intros x hx
  simp [hx]
`);
  const message = failure(`
theorem reused (A B : Set)
  shows A ∩ B ⊆ A ∩ B
proof
  set A := A ∩ B with h
  intros x hx
  exact hx
`);
  assert.match(message, /set .*A is already in scope/u);
});

test("membership in a natural number and in ℕ carry naturality to every guard", () => {
  checks(`
theorem usesNat (i : Nat)
  shows i = i
proof
  rfl

theorem fromMember (k : Nat)
  shows ∀ i ∈ k, i = i
proof
  intros i index
  exact usesNat at i with *

theorem fromMemberGuard (k : Nat)
  shows ∀ i ∈ k, i = i
proof
  intros i index
  have e := usesNat at i
  exact e

theorem fromOmega (n : Set)
  requires hn : n ∈ ℕ
  shows n = n
proof
  exact usesNat at n with *

theorem toOmega (n : Nat)
  shows n ∈ ℕ
proof
  exact nat.omega.forward with *

theorem inOmega (n : Set)
  requires hn : n ∈ ℕ
  shows Nat(n)
proof
  exact nat.omega.backward with *
`);
});

test("a fact proved before induction stays available in the cases", () => {
  checks(`
theorem keptFact (n : Nat) (A B : Set)
  requires sub : A ⊆ B
  shows A ⊆ B
proof
  have again : A ⊆ B := sub
  induction n
  | zero =>
    exact again
  | succ(k) using ih =>
    exact again
`);
  const message = failure(`
theorem droppedFact (n : Nat) (A : Set)
  shows A ⊆ A
proof
  have mentions : n = n by rfl
  induction n
  | zero =>
    intros x hx
    exact hx
  | succ(k) using ih =>
    intros x hx
    exact hx
`);
  assert.match(message, /mentions.*induction variable n/u);
});

test("a forward reference names the later declaration in this module", () => {
  const message = failure(`
theorem early (A : Set)
  shows A ⊆ A
proof
  exact later at A

theorem later (A : Set)
  shows A ⊆ A
proof
  intros x hx
  exact hx
`);
  assert.match(message, /later.*declared later in this module \(line 10\)/u);
  assert.doesNotMatch(message, /does not import/u);
});
