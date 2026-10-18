// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import { readFileSync } from "node:fs";
import assert from "node:assert/strict";
import { canonicalCumulusSourcePath, changedTextParts, checkedFileProofState, diagnosticIdentifier, diagnosticSpan, equivalenceClassNotationAtTextOffset, isFoundationInternalFile, kernelFitchOrder, localTypeAtTextOffset, matchingTacticPrefixLength, migrateCumulusModuleNames, migratePersistedCumulusFiles, notationAtTextOffset, notationForOperandTypes, notationOperandTypeAtTextOffset, notationTypeLabel, orderedPairNotationAtTextOffset, preferredProjectFile, proofDeclarationContext, proofMapSections, qualifiedSymbolCompletions, resolveSymbolCandidate, setNotationAtTextOffset, shouldRetainLastGoal, subscriptNotationAtTextOffset, tacticStepAtCursor, tacticTokenAtTextOffset, tokenAtTextOffset, unicodeCompletionAt, visibleTacticSteps, workspaceFilesForCheck } from "../workbench/editor-utils.js";

test("kernel proofs linearize premises before conclusions without duplicating shared nodes", () => {
  const nodes = [
    { id: 0, children: [1, 2], conclusion: "C" },
    { id: 1, children: [3], conclusion: "A → C" },
    { id: 2, children: [3], conclusion: "A" },
    { id: 3, children: [], conclusion: "A" },
  ];
  const ordered = kernelFitchOrder(nodes);
  assert.deepEqual(ordered.map(node => node.id), [3, 1, 2, 0]);
  assert.deepEqual(ordered.map(node => node.fitchLine), [1, 2, 3, 4]);
});

test("hover information belongs only to the token under the pointer", () => {
  assert.deepEqual(tokenAtTextOffset("alpha   beta", 2), { text: "alpha", start: 0, end: 5 });
  assert.equal(tokenAtTextOffset("alpha   beta", 5), undefined);
  assert.equal(tokenAtTextOffset("alpha   beta", 7), undefined);
  assert.deepEqual(tokenAtTextOffset("alpha   beta", 9), { text: "beta", start: 8, end: 12 });
  assert.deepEqual(tokenAtTextOffset("alpha-beta", 2), { text: "alpha", start: 0, end: 5 });
  assert.equal(tokenAtTextOffset("alpha-beta", 5), undefined);
  assert.deepEqual(tokenAtTextOffset("alpha-beta", 7), { text: "beta", start: 6, end: 10 });
});

test("tactic hover is command-position aware", () => {
  const names = ["cases", "exfalso", "apply", "calc", "exact?"];
  const source = "proof\n  cases h with hp | hq\n  exfalso\n  apply fact\n  calc\n    _ = y := h\n  exact apply(f, x)\n  exact?";
  const at = (needle: string, occurrence = 0) => {
    let offset = -1;
    for (let index = 0; index <= occurrence; index += 1) offset = source.indexOf(needle, offset + 1);
    return offset;
  };
  assert.equal(tacticTokenAtTextOffset(source, at("cases") + 1, names)?.text, "cases");
  assert.equal(tacticTokenAtTextOffset(source, at("exfalso") + 1, names)?.text, "exfalso");
  assert.equal(tacticTokenAtTextOffset(source, at("apply") + 1, names)?.text, "apply");
  assert.equal(tacticTokenAtTextOffset(source, at("calc") + 1, names)?.text, "calc");
  assert.equal(tacticTokenAtTextOffset(source, at("apply", 1) + 1, names), undefined);
  assert.equal(tacticTokenAtTextOffset(source, at("exact?") + 5, names)?.text, "exact?");
});

test("incomplete instance proofs retain their own declaration identity", () => {
  const source = `theorem before
  shows P
proof
  exact p

instance chosen
  shows HasChoice(A)
proof
  apply constructor

lemma after
  shows Q
proof
  exact q`;
  assert.deepEqual(proofDeclarationContext(source, 9), {
    name: "chosen", lineStart: 6, lineEnd: 10, statement: "HasChoice(A)",
  });
  assert.deepEqual(proofDeclarationContext(source, 12), {
    name: "after", lineStart: 11, lineEnd: 14, statement: "Q",
  });
  assert.equal(proofDeclarationContext(`${source}\n\ndef value : Set := x\n  broken`, 17), undefined);
  assert.deepEqual(proofDeclarationContext("theorem\n  shows P\nproof", 3), {
    name: "Incomplete proof", lineStart: 1, lineEnd: 3, statement: "P",
  });
});

test("checked import-only modules receive the proven file state", () => {
  assert.equal(checkedFileProofState({ theorems: 0, definitions: 0, sorries: 0, admittedSorries: 0 }), "proven");
  assert.equal(checkedFileProofState({ theorems: 0, definitions: 0, sorries: 1, admittedSorries: 1 }), "sorry");
  assert.equal(checkedFileProofState(undefined), undefined);
});

test("qualified completion discovers checked names by namespace suffix", () => {
  const names = [
    "Grace.Cumulus.Cardinal.Finite.omega.infinite",
    "Grace.Cumulus.Cardinal.Finite.omega.order_unbounded",
    "Grace.Cumulus.NumberTheory.primes.infinite",
  ];
  assert.deepEqual(qualifiedSymbolCompletions(names, "exact omega.").map(item => item.label), [
    "omega.infinite", "omega.order_unbounded",
  ]);
  assert.deepEqual(qualifiedSymbolCompletions(names, "exact omega.i").map(item => item.insertText), ["infinite"]);
  assert.deepEqual(qualifiedSymbolCompletions(names, "exact primes.").map(item => item.label), ["primes.infinite"]);
});

test("a function call is not shadowed by a same-named theorem", () => {
  const symbols = [
    { name: "Grace.Cumulus.Set.Ordinal.next", short: "next", kind: "definition", file: "Ordinal.g17", line: 14 },
    { name: "Grace.Cumulus.Set.Ordinal.Ordinal.next", short: "Ordinal.next", kind: "theorem", file: "Ordinal.g17", line: 61 },
  ];
  const context = {
    module: "Grace.Cumulus.Set.Ordinal",
    file: "Ordinal.g17",
    theorem: "Grace.Cumulus.Set.Ordinal.Ordinal.next",
  };
  assert.equal(resolveSymbolCandidate(symbols, "next", { ...context, call: true })?.kind, "definition");
  assert.equal(resolveSymbolCandidate(symbols, "Ordinal.next", context)?.kind, "theorem");
});

test("notation hover selects the longest notation genuinely under the pointer", () => {
  const notations = [{ token: "<" }, { token: "<->" }, { token: "×" }];
  assert.deepEqual(notationAtTextOffset("A × B", 2, notations), { text: "×", start: 2, end: 3 });
  assert.deepEqual(notationAtTextOffset("p <-> q", 3, notations), { text: "<->", start: 2, end: 5 });
  assert.equal(notationAtTextOffset("A × B", 1, notations), undefined);
});

test("mixfix notation hover finds the literal under the pointer only inside a complete pattern", () => {
  const notations = [{ token: "_ : _ → _", fixity: "mixfix", target: "FunctionBetween", kind: "predicate" }, { token: "⊆" }];
  const text = "theorem t (f A B : Set) (g : B → C)\n  requires hf : f : A -> B\n  requires hs : A ⊆ B\n  shows Nat(n) → n ∈ S\n  have h : compose(g, f, A, B, C) : A → C := value with *\n";
  const at = (probe: string) => text.indexOf(probe);
  const mixfix = (start: number, end: number) => ({ text: "_ : _ → _", start, end, mixfix: true });
  assert.deepEqual(notationAtTextOffset(text, at("-> B"), notations), mixfix(at("-> B"), at("-> B") + 2));
  assert.deepEqual(notationAtTextOffset(text, at(": A -> B"), notations), mixfix(at(": A -> B"), at(": A -> B") + 1));
  assert.deepEqual(notationAtTextOffset(text, at("→ C)"), notations), mixfix(at("→ C)"), at("→ C)") + 1));
  assert.deepEqual(notationAtTextOffset(text, at("→ C :="), notations), mixfix(at("→ C :="), at("→ C :=") + 1));
  assert.equal(notationAtTextOffset(text, at("→ n ∈ S"), notations), undefined);
  assert.equal(notationAtTextOffset(text, at(": f : A"), notations), undefined);
  assert.deepEqual(notationAtTextOffset(text, at("⊆"), notations), { text: "⊆", start: at("⊆"), end: at("⊆") + 1 });
});

test("goal notation hover selects its carrier from soft-type assumptions", () => {
  const notations = [
    { token: "0", target: "rationalZero", operandType: "Rational" },
    { token: "0", target: "realZero", operandType: "Real" },
    { token: "≤", target: "LessEqual", operandType: "Nat" },
    { token: "≤", target: "relates", operandType: "Real",
      leadingArguments: [{ tag: "app", fn: "realLe", args: [] }] },
  ];
  const text = "0 ≤ (A * A)";
  assert.equal(notationOperandTypeAtTextOffset(text,
    { text: "0", start: 0, end: 1 }, [{ formula: "A ∈ Real" }], notations), "Real");
  assert.equal(notationOperandTypeAtTextOffset(text,
    { text: "≤", start: 2, end: 3 }, [{ formula: "A ∈ Real" }], notations), "Real");
});

test("notation hover resolves heterogeneous operand signatures", () => {
  const natural = { token: "^", target: "pow", operandType: "Nat" };
  const real = {
    token: "^", target: "realPow",
    leftOperandType: "Real", rightOperandType: "Nat",
  };
  assert.equal(notationForOperandTypes([natural, real], "Real", "Nat"), real);
  assert.equal(notationForOperandTypes([natural, real], "Nat", "Nat"), natural);
  assert.equal(notationTypeLabel(real), "Real, Nat");
});

test("notation hover cost is independent of the source prefix", () => {
  const source = `${"x < ".repeat(250_000)}target`;
  const notations = ["<", "<->", "+", "*", "⊆", "∈"].map(token => ({ token }));
  const started = performance.now();
  for (let index = 0; index < 1_000; index += 1) {
    assert.equal(notationAtTextOffset(source, source.length - 2, notations), undefined);
  }
  assert.ok(performance.now() - started < 150,
    "hover lookup must inspect only the characters that can cover the pointer");
});

test("local soft-type hover scans binders without constructing a dynamic regex", () => {
  const source = `-- Density and unboundedness\ntheorem dense (q r : Rational)\nproof\n  have midpoint : Rational(q + r)\n  exact q + midpoint`;
  const token = (text: string, occurrence = 0) => {
    let start = -1;
    for (let index = 0; index <= occurrence; index += 1) start = source.indexOf(text, start + 1);
    return { text, start, end: start + text.length };
  };
  assert.equal(localTypeAtTextOffset(source, token("q", 2)), "Rational");
  assert.equal(localTypeAtTextOffset(source, token("midpoint", 1)), "Rational");
  assert.doesNotThrow(() => localTypeAtTextOffset(source, token("Density")));
  assert.equal(localTypeAtTextOffset(source, token("Density")), undefined);
});

test("set notation hover exposes the exact finite-literal elaboration", () => {
  assert.deepEqual(setNotationAtTextOffset("∅", 0), {
    text: "∅", start: 0, end: 1, target: "empty", literal: "∅", literalStart: 0, literalEnd: 1,
    elements: [], desugaring: "empty",
  });
  assert.deepEqual(setNotationAtTextOffset("{x}", 0), {
    text: "{", start: 0, end: 1, target: "singleton", literal: "{x}", literalStart: 0, literalEnd: 3,
    elements: ["x"], desugaring: "singleton(x)",
  });
  assert.deepEqual(setNotationAtTextOffset("{x}", 2), {
    text: "}", start: 2, end: 3, target: "singleton", literal: "{x}", literalStart: 0, literalEnd: 3,
    elements: ["x"], desugaring: "singleton(x)",
  });
  assert.deepEqual(setNotationAtTextOffset("{x, y, z}", 0), {
    text: "{", start: 0, end: 1, target: "union2", literal: "{x, y, z}", literalStart: 0, literalEnd: 9,
    elements: ["x", "y", "z"], desugaring: "union2(singleton(x), pair(y, z))",
  });
  assert.equal(setNotationAtTextOffset("{{x}, y}", 7)?.desugaring, "pair({x}, y)");
  assert.equal(setNotationAtTextOffset("{x in A | p(x)}", 0), undefined);
});

test("ordered-pair punctuation exposes its exact elaboration without capturing calls", () => {
  const source = "(x, (y, z))";
  assert.equal(orderedPairNotationAtTextOffset(source, 0)?.desugaring, "orderedPair(x, (y, z))");
  assert.equal(orderedPairNotationAtTextOffset(source, 2)?.desugaring, "orderedPair(x, (y, z))");
  // A comma after a binder is not a pair: the group is a quantified formula.
  const quantified = "none : ¬(∃ m, Maximal(A, r, m))";
  assert.equal(orderedPairNotationAtTextOffset(quantified, quantified.indexOf("(")), undefined);
  assert.equal(orderedPairNotationAtTextOffset(quantified, quantified.indexOf(",")), undefined);
  const universal = "(∀ x ∈ A, x ∈ B)";
  assert.equal(orderedPairNotationAtTextOffset(universal, 0), undefined);
  assert.equal(orderedPairNotationAtTextOffset(source, 4)?.desugaring, "orderedPair(y, z)");
  assert.equal(orderedPairNotationAtTextOffset(source, 6)?.desugaring, "orderedPair(y, z)");
  assert.equal(orderedPairNotationAtTextOffset(source, 9)?.desugaring, "orderedPair(y, z)");
  assert.equal(orderedPairNotationAtTextOffset("f(x, y)", 3), undefined);
  assert.equal(orderedPairNotationAtTextOffset("(x : Set)", 0), undefined);
});

test("equivalence-class notation hover exposes its constructor order", () => {
  const source = "⟦x⟧[A, r]";
  for (const offset of [0, 2]) assert.deepEqual(equivalenceClassNotationAtTextOffset(source, offset), {
    text: source[offset], start: offset, end: offset + 1, target: "equivalenceClass",
    literal: source, literalStart: 0, literalEnd: source.length,
    desugaring: "equivalenceClass(A, r, x)",
  });
});

test("subscript notation hover exposes function application", () => {
  assert.equal(subscriptNotationAtTextOffset("uₙ + vₙ", 1)?.desugaring, "apply(u, n)");
  assert.equal(subscriptNotationAtTextOffset("uₙ + vₙ", 0)?.desugaring, "apply(u, n)");
  assert.equal(subscriptNotationAtTextOffset("u[n + 1]", 4)?.desugaring, "apply(u, n + 1)");
  assert.equal(subscriptNotationAtTextOffset("M[i, j]", 3)?.desugaring,
    "apply(M, orderedPair(i, j))");
  assert.equal(subscriptNotationAtTextOffset("M[f(i, j), k]", 5)?.desugaring,
    "apply(M, orderedPair(f(i, j), k))");
  assert.equal(subscriptNotationAtTextOffset("M[(i, j)]", 3)?.desugaring,
    "apply(M, (i, j))");
});

test("cursor selection distinguishes tactic spans on the same source line", () => {
  const steps = [
    { line: 8, columnStart: 3 },
    { line: 9, columnStart: 3 },
    { line: 9, columnStart: 24 },
    { line: 9, columnStart: 31 },
  ];
  assert.equal(tacticStepAtCursor(steps, 9, 8), 2);
  assert.equal(tacticStepAtCursor(steps, 9, 25), 3);
  assert.equal(tacticStepAtCursor(steps, 9, 35), 4);
});

test("cursor navigation retains the last checked trace while a new check is pending", () => {
  const steps = [
    { line: 2, columnStart: 3, command: "intro h" },
    { line: 3, columnStart: 3, command: "exact h" },
  ];
  const checked = "proof\n  intro h\n  exact h";
  const edited = "proof\n  changed\n  exact h";
  assert.equal(visibleTacticSteps(steps, checked, edited, false).length, 2);
  assert.equal(visibleTacticSteps(steps, checked, edited, true).length, 0);
});

test("matching tactic prefixes accepts authored dot bullets", () => {
  const steps = [{ line: 2, columnStart: 3, command: "exact h" }];
  assert.equal(matchingTacticPrefixLength(steps, "proof\n  . exact h"), 1);
});

test("proof map sections contain the checked tactics in their authored hierarchy", () => {
  const entries = [
    { line: 5, indent: 2, kind: "heading", text: "Split" },
    { line: 6, indent: 2, kind: "note", text: "Two branches." },
    { line: 8, indent: 4, kind: "heading", text: "Left" },
    { line: 11, indent: 4, kind: "heading", text: "Right" },
  ];
  const steps = [
    { line: 7, command: "constructor", after: { goals: [{}, {}] } },
    { line: 9, command: "rfl", after: { goals: [{}] } },
    { line: 12, command: "rfl", after: { goals: [] } },
  ];
  const map = proofMapSections(entries, steps);
  assert.deepEqual(map.sections.map(section => [section.text, section.steps.map(step => step.command)]), [["Split", ["constructor"]]]);
  assert.deepEqual(map.sections[0].sections.map(section => [section.text, section.steps.map(step => step.command)]), [
    ["Left", ["rfl"]], ["Right", ["rfl"]],
  ]);
  assert.equal(map.sections[0].notes[0].text, "Two branches.");
});

test("transient source errors retain an available last valid goal", () => {
  assert.equal(shouldRetainLastGoal({ hasTrace: false, hasResult: true, errorBelongsToFile: true, theoremCount: 1 }), true);
  assert.equal(shouldRetainLastGoal({ hasTrace: true, hasResult: true, errorBelongsToFile: true, theoremCount: 1 }), false);
  assert.equal(shouldRetainLastGoal({ hasTrace: false, hasResult: false, errorBelongsToFile: true, theoremCount: 1 }), false);
  assert.equal(shouldRetainLastGoal({ hasTrace: false, hasResult: true, errorBelongsToFile: false, theoremCount: 1 }), false);
});

test("editor diagnostics identify and select the complete offending token", () => {
  const message = "unknown variable or constant omegasda";
  assert.equal(diagnosticIdentifier(message), "omegasda");
  assert.equal(diagnosticIdentifier("unknown theorem `missing.fact`"), "missing.fact");
  assert.deepEqual(diagnosticSpan("  shows pair(x, omegasda)", message), {
    identifier: "omegasda", startColumn: 17, endColumn: 25,
  });
  assert.deepEqual(diagnosticSpan("short", message, 99), {
    identifier: "omegasda", startColumn: 6, endColumn: 6,
  });
});

test("backslash commands expand to editor Unicode at the cursor", () => {
  assert.deepEqual(unicodeCompletionAt("x \\in", 5),
    { start: 2, end: 5, symbol: "∈", command: "in" });
  assert.deepEqual(unicodeCompletionAt("shows \\not", 10),
    { start: 6, end: 10, symbol: "¬", command: "not" });
  assert.deepEqual(unicodeCompletionAt("shows \\forall", 13),
    { start: 6, end: 13, symbol: "∀", command: "forall" });
  assert.deepEqual(unicodeCompletionAt("P \\imp", 6),
    { start: 2, end: 6, symbol: "→", command: "imp" });
  assert.deepEqual(unicodeCompletionAt("P \\lr", 5),
    { start: 2, end: 5, symbol: "↔", command: "lr" });
  assert.deepEqual(unicodeCompletionAt("shows\n  c\n  \\and", 16),
    { start: 12, end: 16, symbol: "∧", command: "and" });
  assert.deepEqual(unicodeCompletionAt("rw \\l", 5),
    { start: 3, end: 5, symbol: "←", command: "l" });
  assert.deepEqual(unicodeCompletionAt("rcases h with \\<", 16),
    { start: 14, end: 16, symbol: "⟨", command: "<" });
  assert.deepEqual(unicodeCompletionAt("natural, equipotent\\>", 21),
    { start: 19, end: 21, symbol: "⟩", command: ">" });
  assert.deepEqual(unicodeCompletionAt("A \\uplus", 8),
    { start: 2, end: 8, symbol: "⊎", command: "uplus" });
  assert.deepEqual(unicodeCompletionAt("A \\simeq", 8),
    { start: 2, end: 8, symbol: "≃", command: "simeq" });
  assert.deepEqual(unicodeCompletionAt("x \\mapsto", 9),
    { start: 2, end: 9, symbol: "↦", command: "mapsto" });
  assert.deepEqual(unicodeCompletionAt("A \\times", 8),
    { start: 2, end: 8, symbol: "×", command: "times" });
  assert.deepEqual(unicodeCompletionAt("R \\restrict", 11),
    { start: 2, end: 11, symbol: "↾", command: "restrict" });
  assert.deepEqual(unicodeCompletionAt("\\bigcup", 7),
    { start: 0, end: 7, symbol: "⋃", command: "bigcup" });
  assert.deepEqual(unicodeCompletionAt("\\int", 4),
    { start: 0, end: 4, symbol: "∫", command: "int" });
  assert.deepEqual(unicodeCompletionAt("\\powerset", 9),
    { start: 0, end: 9, symbol: "𝒫", command: "powerset" });
  assert.deepEqual(unicodeCompletionAt("A \\cup", 6),
    { start: 2, end: 6, symbol: "∪", command: "cup" });
  assert.deepEqual(unicodeCompletionAt("A \\cap", 6),
    { start: 2, end: 6, symbol: "∩", command: "cap" });
  assert.deepEqual(unicodeCompletionAt("A \\setminus", 11),
    { start: 2, end: 11, symbol: "∖", command: "setminus" });
  assert.deepEqual(unicodeCompletionAt("A \\quot", 7),
    { start: 2, end: 7, symbol: "⧸", command: "quot" });
  assert.deepEqual(unicodeCompletionAt("x ∈ \\mathbb{N}", 14),
    { start: 4, end: 14, symbol: "ℕ", command: "mathbb{N}" });
  assert.deepEqual(unicodeCompletionAt("A \\subset", 9),
    { start: 2, end: 9, symbol: "⊆", command: "subset" });
  assert.deepEqual(unicodeCompletionAt("A \\psubset", 10),
    { start: 2, end: 10, symbol: "⊂", command: "psubset" });
  assert.deepEqual(unicodeCompletionAt("u\\_n", 4),
    { start: 1, end: 4, symbol: "ₙ", command: "_n" });
  assert.deepEqual(unicodeCompletionAt("a\\_1", 4),
    { start: 1, end: 4, symbol: "₁", command: "_1" });
  assert.equal(unicodeCompletionAt("unknown \\xyz", 12), undefined);
});

test("edited source exposes only the still-present checked tactic prefix", () => {
  const steps = [
    { line: 7, columnStart: 3, columnEnd: 10, command: "intro x" },
    { line: 8, columnStart: 3, columnEnd: 15, command: "constructor" },
    { line: 9, columnStart: 3, columnEnd: 10, command: "exact h" },
  ];
  assert.equal(matchingTacticPrefixLength(steps, "\n\n\n\n\n\n  intro x\n  constructor\n  exact h"), 3);
  assert.equal(matchingTacticPrefixLength(steps, "\n\n\n\n\n\n  intro x\n\n  exact h"), 1);
});

test("edited source recognizes a checked tactic spanning physical lines", () => {
  const steps = [{
    line: 4, columnStart: 3, columnEnd: 80,
    command: "settle with next.natural, next.membership, Naturals.constructor.zero, Naturals.constructor.succ",
  }];
  const source = "theorem t\n  shows 2 in 5\nproof\n  settle with next.natural, next.membership,\n    Naturals.constructor.zero, Naturals.constructor.succ";
  assert.equal(matchingTacticPrefixLength(steps, source), 1);
});

test("edited source recognizes a with clause on its own indented line", () => {
  const steps = [{ line: 4, columnStart: 3, columnEnd: 28, command: "exact fact with y, hy" }];
  const source = "theorem t\n  shows x = x\nproof\n  exact fact\n    with y, hy";
  assert.equal(matchingTacticPrefixLength(steps, source), 1);
});

test("goal change highlighting never invents an empty-set symbol for deletions", () => {
  assert.deepEqual(changedTextParts("pairXX : p ∈ A", "pairXX : ∅p ∈ A"),
    { prefix: "pairXX : ", changed: "", suffix: "p ∈ A" });
});

test("stale persisted library tabs do not shadow current bundled imports", () => {
  const files = [
    { id: "sum", name: "Sum.g17", source: "module Grace.Cumulus.Cardinal.Sum\nimport Grace.Cumulus.Function" },
    { id: "old-function", name: "Function.g17", source: "module Grace.Cumulus.Function\ndef oldOnly : Set := 0" },
    { id: "custom", name: "MyLemma.g17", source: "module MyLemma\nimport Grace.Cumulus.Function" },
  ];
  assert.deepEqual(workspaceFilesForCheck(files, "sum", "0.56.0").map(file => file.name), ["Sum.g17", "MyLemma.g17"]);
  files[1].dirty = true;
  assert.deepEqual(workspaceFilesForCheck(files, "sum", "0.56.0").map(file => file.name), ["Sum.g17", "Function.g17", "MyLemma.g17"]);
});

test("clean Cumulus views never override bundled dependencies", () => {
  const files = [
    { id: "order", name: "lib/Grace/Cumulus/Order.g17", source: "module Grace.Cumulus.Order", distribution: "cumulus", openedIn: "0.99.30" },
    { id: "set", name: "lib/Grace/Cumulus/Set.g17", source: "module Grace.Cumulus.Set\n-- stale clean view", distribution: "cumulus", openedIn: "0.99.30", dirty: false },
  ];
  assert.deepEqual(workspaceFilesForCheck(files, "order", "0.99.30").map(file => file.name), [files[0].name]);
  files[1].dirty = true;
  assert.deepEqual(workspaceFilesForCheck(files, "order", "0.99.30").map(file => file.name), [files[0].name, files[1].name]);
});

test("persisted Cumulus number systems migrate out of the obsolete Data namespace", () => {
  assert.equal(
    canonicalCumulusSourcePath("lib/Grace/Cumulus/Data/Real/Defs.g17"),
    "lib/Grace/Cumulus/Real/Defs.g17",
  );
  assert.equal(canonicalCumulusSourcePath("Data/Real/Defs.g17"), "Data/Real/Defs.g17");
  assert.equal(
    migrateCumulusModuleNames("module Grace.Cumulus.Data.Real.Defs\nimport Grace.Cumulus.Data.Rat.Order"),
    "module Grace.Cumulus.Real.Defs\nimport Grace.Cumulus.Rat.Order",
  );

  const bundled = new Map([
    ["lib/Grace/Cumulus/Real/Defs.g17", "module Grace.Cumulus.Real.Defs\n-- current distribution"],
  ]);
  const files = [
    {
      id: "clean", name: "lib/Grace/Cumulus/Data/Real/Defs.g17",
      sourceFile: "lib/Grace/Cumulus/Data/Real/Defs.g17", projectPath: "Data/Real/Defs.g17",
      source: "module Grace.Cumulus.Data.Real.Defs\n-- stale", distribution: "cumulus", dirty: false,
    },
    {
      id: "edited", name: "lib/Grace/Cumulus/Data/Real/Defs.g17",
      sourceFile: "lib/Grace/Cumulus/Data/Real/Defs.g17", projectPath: "Data/Real/Defs.g17",
      source: "module Grace.Cumulus.Data.Real.Defs\n-- my edit", distribution: "cumulus", dirty: true,
    },
  ];
  migratePersistedCumulusFiles(files, bundled, "0.99.30");
  assert.deepEqual(files.map(file => ({
    name: file.name, sourceFile: file.sourceFile, projectPath: file.projectPath,
    source: file.source, dirty: file.dirty, openedIn: file.openedIn,
  })), [
    {
      name: "lib/Grace/Cumulus/Real/Defs.g17", sourceFile: "lib/Grace/Cumulus/Real/Defs.g17",
      projectPath: "Real/Defs.g17", source: "module Grace.Cumulus.Real.Defs\n-- my edit",
      dirty: true, openedIn: "0.99.30",
    },
  ]);
});

test("legacy project-relative Cumulus number tabs migrate and deduplicate", () => {
  const bundled = new Map([
    ["lib/Grace/Cumulus/Real/Core.g17", "module Grace.Cumulus.Real.Core\nimport Grace.Cumulus.Real.Defs"],
  ]);
  const files = [
    {
      id: "current", name: "lib/Grace/Cumulus/Real/Core.g17",
      sourceFile: "lib/Grace/Cumulus/Real/Core.g17", projectPath: "Real/Core.g17",
      source: "module Grace.Cumulus.Real.Core\n-- stale current path", distribution: "cumulus", dirty: false,
    },
    {
      id: "legacy", name: "Data/Real/Core.g17",
      sourceFile: "Data/Real/Core.g17", projectPath: "Data/Real/Core.g17",
      source: "module Grace.Cumulus.Data.Real.Core\nimport Grace.Cumulus.Data.Real.Defs",
      distribution: "cumulus", dirty: false,
    },
  ];
  migratePersistedCumulusFiles(files, bundled, "0.99.30");
  assert.equal(files.length, 1);
  assert.equal(files[0].name, "lib/Grace/Cumulus/Real/Core.g17");
  assert.equal(files[0].projectPath, "Real/Core.g17");
  assert.equal(files[0].source, "module Grace.Cumulus.Real.Core\nimport Grace.Cumulus.Real.Defs");
});

test("complete library folders open authored mathematics before foundation internals", () => {
  const files = [
    { id: "aliases", name: "Bootstrap/Aliases.g17" },
    { id: "foundation", name: "Kernel/Foundation.g17" },
    { id: "core", name: "Core.g17" },
    { id: "main", name: "Cumulus/Main.g17" },
  ];
  assert.equal(isFoundationInternalFile(files[0].name), true);
  assert.equal(isFoundationInternalFile(files[1].name), true);
  assert.equal(isFoundationInternalFile(files[2].name), false);
  assert.equal(preferredProjectFile(files)?.id, "main");
  assert.equal(preferredProjectFile([{ id: "first", name: "MyProject.g17" }, { id: "second", name: "Other.g17" }])?.id, "first");
});


test("declared coordinate subscripts stay identifiers while undeclared suffixes remain indexing", () => {
  const source = `theorem coordinates (a₁ b₂ : Real)
  shows a₁ = b₂
proof
  sorry

theorem sequence (u : Set)
  shows u₂ = u[2]
proof
  rfl`;
  assert.equal(subscriptNotationAtTextOffset(source, source.indexOf("a₁")), undefined);
  assert.equal(subscriptNotationAtTextOffset(source, source.indexOf("b₂", source.indexOf("shows"))), undefined);
  assert.equal(subscriptNotationAtTextOffset(source, source.indexOf("u₂"))?.desugaring, "apply(u, 2)");
  assert.equal(subscriptNotationAtTextOffset("a₁ ∈ ℝ", 0, ["a₁"]), undefined);
  assert.deepEqual(tokenAtTextOffset("b₂", 1), { text: "b₂", start: 0, end: 2 });
});

test("the actual Monaco grammar keeps subscripted coordinates intact", async () => {
  const { compile } = await import("../node_modules/monaco-editor/esm/vs/editor/standalone/common/monarch/monarchCompile.js");
  const source = readFileSync("workbench/app.js", "utf8");
  const start = source.indexOf('  monaco.languages.setMonarchTokensProvider("grace17", {');
  assert.ok(start >= 0);
  const end = source.indexOf("\n  });", start) + 6;
  let grammar;
  new Function("monaco", source.slice(start, end))({ languages: {
    setMonarchTokensProvider: (_id, value) => { grammar = value; },
  } });
  const lexer = compile("grace17", grammar);
  for (const [word, expected] of [["by", "keyword.connective"], ["b₂", "identifier"], ["a₁", "identifier"], ["byReal", "identifier"]]) {
    const rule = lexer.tokenizer.root.find(rule => rule.regex.test(word));
    const match = word.match(rule.regex);
    assert.equal(match[0], word);
    assert.equal(rule.action.test(word, match, "root", true), expected);
  }
});

test("directional proof hovers preserve source targets and refuse ambiguous bases", () => {
  const left = { name: "Left.fact", short: "fact", kind: "theorem", file: "Left.g17", line: 3,
    directions: { forward: "P → Q", backward: "Q → P" } };
  const right = { ...left, name: "Right.fact", file: "Right.g17" };
  const projected = resolveSymbolCandidate([left], "fact.backward");
  assert.equal(projected.name, "Left.fact.backward");
  assert.equal(projected.file, left.file);
  assert.equal(projected.line, left.line);
  assert.match(projected.info, /Q → P/);
  assert.equal(resolveSymbolCandidate([left, right], "fact.forward"), undefined);
  assert.equal(resolveSymbolCandidate([{ ...left, directions: undefined }], "fact.forward"), undefined);
  const explicit = { ...left, name: "Left.fact.forward", short: "fact.forward", info: "Explicit declaration" };
  assert.equal(resolveSymbolCandidate([left, explicit], "Left.fact.forward"), explicit);
});
