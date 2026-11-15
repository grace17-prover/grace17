// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

// A section hypothesis is a premise of every theorem of the section. The
// check keeps it so and warns when a theorem's proof does not use it.
const source = `module Warn
predicate Good (S : Set) := S = S
predicate Fine (S : Set) := S = S

section Facts
variable (A B : Set)
hypothesis good : Good(A)
hypothesis fine : Fine(B)

theorem usesBoth
  shows Good(A) ∧ Fine(B)
proof
  exact ⟨good, fine⟩

theorem usesOne (x : Set)
  requires member : x ∈ A
  shows x ∈ A ∧ Good(A)
proof
  exact ⟨member, good⟩

theorem usesNone (x : Set)
  requires member : x ∈ A
  shows x ∈ A
proof
  exact member

end Facts
`;

test("a section hypothesis a proof does not use is reported, and the premise stays", () => {
  const kernel = createZfKernel();
  const [loaded] = loadModuleSourceGraph(kernel, [{ file: "Warn.g17", source }], ["lib"]);
  const warnings = loaded!.warnings;
  assert.deepEqual(warnings.map(item => [item.theorem, item.line]), [["Warn.usesOne", 15], ["Warn.usesNone", 21], ["Warn.usesNone", 21]]);
  assert.match(warnings[0]!.message, /^section hypothesis fine is a premise of usesOne that its proof does not use and that shares no variable with its statement$/);
  assert.match(warnings[1]!.message, /^section hypothesis good is a premise of usesNone that its proof does not use$/);
  assert.match(warnings[2]!.message, /^section hypothesis fine is a premise of usesNone that its proof does not use and that shares no variable/);
  // The signatures and the premises are unchanged by the warning.
  const statement = kernel.theorems.get("Warn.usesNone")!;
  let premises = 0;
  for (let spine = statement; ; ) {
    if (spine.tag === "forall") { spine = spine.body; continue; }
    if (spine.tag === "imp") { premises += 1; spine = spine.right; continue; }
    break;
  }
  assert.equal(premises, 3);
});
