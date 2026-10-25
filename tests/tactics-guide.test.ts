// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { declarationHelpAtTextOffset, documentedTacticFamilies, helpInferenceRule, highlightGrace17, tacticGuideSections, tacticHelpEntries } from "../workbench/tactics-guide.js";
import { tacticReference, tacticReferenceNotes } from "../workbench/tactics-reference.js";
import { renderTacticsDoc } from "../scripts/update-tactics-doc.ts";

test("the Workbench guide contains every built-in tactic family", () => {
  const expected = [
    "exact?", "apply?", "rw?", "sorry", "ext", "simp", "simpa", "rewrite", "rw", "unfold",
    "induction", "obtain", "have", "calc", "specialize", "apply", "exact", "intro", "intros", "left", "right",
    "constructor", "split", "refine", "rcases", "cases", "clear", "rename", "revert", "set", "exfalso",
    "by_contra", "by_cases", "contradiction", "tauto", "cc", "congruence", "witness", "use", "assumption",
    "reflexivity", "rfl", "compute", "decide", "linear_combination", "ring_nf", "ring", "arith", "linarith",
    "settle", "typecheck", "synthesize", "tactic",
  ];
  assert.deepEqual(documentedTacticFamilies, expected);
  const syntax = tacticGuideSections.flatMap(section => section.entries.map(entry => entry.syntax)).join("\n");
  for (const family of expected) assert.match(syntax, new RegExp(`(^|[^A-Za-z_])${family.replace(/[?]/g, "\\?")}([^A-Za-z_]|$)`), family);
});

test("Help documents proof-producing inequality calculations", () => {
  const calc = tacticGuideSections.flatMap(section => section.entries)
    .find(entry => entry.syntax === "calc");
  assert.ok(calc);
  assert.match(calc.detail, /mixed strict and non-strict order/);
  assert.match(calc.detail, /equality steps within an inequality chain/);
  assert.match(calc.detail, /Tau/);
  assert.match(calc.detail, /kernel unchanged/);
  const tactics = readFileSync(new URL("../docs/tactics.md", import.meta.url), "utf8");
  assert.match(tactics, /Strict rational and real inequalities/);
  assert.match(tactics, /mixed compositions `<` followed by `≤`/);
});

test("docs/tactics.md is rendered from the Workbench Help", () => {
  assert.equal(readFileSync(new URL("../docs/tactics.md", import.meta.url), "utf8"), renderTacticsDoc());
  for (const section of tacticGuideSections) {
    if (section.id === "language" || section.kind === "language") continue;
    for (const entry of section.entries) {
      assert.ok(Array.isArray(tacticReferenceNotes(entry.syntax)), entry.syntax);
    }
  }
  const syntaxes = new Set(tacticGuideSections.flatMap(section => section.entries.map(entry => entry.syntax)));
  for (const syntax of tacticReference.keys()) assert.ok(syntaxes.has(syntax), `reference note for unknown entry: ${syntax}`);
});

test("Help begins with the language, builds from small moves, and ends with induction", () => {
  assert.equal(tacticGuideSections[0]?.id, "language");
  assert.equal(tacticGuideSections[1]?.id, "first-moves");
  assert.equal(tacticGuideSections.at(-1)?.id, "induction");
  for (const section of tacticGuideSections) {
    for (const entry of section.entries) {
      assert.ok(entry.example?.trim(), `${section.id}: ${entry.syntax} needs a concrete example`);
    }
  }
});

test("the guide distinguishes all four induction interfaces", () => {
  const induction = tacticGuideSections.find(section => section.id === "induction");
  assert.equal(induction?.entries.length, 4);
  const text = JSON.stringify(induction);
  assert.match(text, /constructors of an inductive datatype/);
  assert.match(text, /induction finite with G a/);
  assert.match(text, /\| insert using ih =>/);
  assert.match(text, /using membership/);
  assert.match(text, /wellFoundedOn/);
  assert.match(text, /∀ x, x ∈ A → P\(x\)/);
  assert.match(text, /Revert assumptions/);
  assert.match(text, /recursive fields/);
});

test("Help explains the local and public scope behavior of export open", () => {
  const language = tacticGuideSections.find(section => section.id === "language");
  const entry = language?.entries.find(item => item.syntax === "export open Module.Name");
  assert.ok(entry);
  assert.match(entry.detail, /current module/);
  assert.match(entry.detail, /modules that import the current module/);
  assert.match(entry.detail, /ordinary open stays local/);
  assert.match(entry.detail, /entrypoint modules/);
  assert.match(entry.example, /export open Grace\.Cumulus\.Set\.Ordinal/);
  assert.equal(helpInferenceRule(entry.syntax), undefined);
});

test("Help covers checked graphs, bounded choice, and quantified rewriting", () => {
  const language = tacticGuideSections.find(section => section.id === "language");
  const graph = language?.entries.find(entry => entry.syntax.startsWith("defgraph "));
  const choice = language?.entries.find(entry => entry.syntax.startsWith("defchoose "));
  assert.ok(graph);
  assert.ok(choice);
  assert.match(graph.detail, /\.closed, \.relates, \.function, and \.value/);
  assert.match(graph.detail, /typed Nat or Real index/);
  assert.match(choice.detail, /checked existence proof/);
  assert.match(choice.detail, /bounded Separation/);
  assert.match(choice.detail, /c\.exists and c\.selected/);
  assert.equal(helpInferenceRule(graph.syntax), undefined);
  assert.equal(helpInferenceRule(choice.syntax), undefined);
  assert.ok(tacticHelpEntries("defgraph").includes(graph));
  assert.ok(tacticHelpEntries("defchoose").includes(choice));
  const rewrite = tacticGuideSections.flatMap(section => section.entries)
    .find(entry => entry.syntax === "rw under h at fact");
  assert.ok(rewrite);
  assert.match(rewrite.detail, /do not depend on that binder's variable/);
  assert.match(rewrite.detail, /equality elimination/);
  assert.equal(helpInferenceRule(rewrite.syntax)?.label, "=E");
});

test("Help explains expression carrier annotations without claiming a typing proof", () => {
  const entry = tacticGuideSections.find(section => section.id === "soft-types")?.entries
    .find(item => item.syntax.includes("(0:R)"));
  assert.ok(entry);
  assert.match(entry.detail, /does not prove membership/);
  assert.match(entry.detail, /conflicting known type/);
  assert.match(entry.example, /\(p\[i\]:R\) < \(p\[succ\(i\)\]:R\)/);
  assert.equal(helpInferenceRule(entry.syntax), undefined);
});

test("Help keeps mathematical classes separate from type classes", () => {
  const classes = tacticGuideSections.find(section => section.id === "classes");
  const text = JSON.stringify(classes);
  assert.match(text, /class is set-theoretic collection syntax, not a type-class declaration/);
  assert.match(text, /not a type-class instance/);
  assert.match(text, /separate via query asks the import-scoped type-class registry/);
  assert.match(text, /separate, untrusted registry scoped by module imports/);
  assert.match(text, /unrelated to the set-theoretic class keyword/);
  assert.match(text, /multiple successful global candidates are an error/);
  assert.match(text, /Tau system/);
  assert.doesNotMatch(text, /class-directed overloading/);
});

test("Help specifies soft typing and bounded quantifiers precisely", () => {
  const section = tacticGuideSections.find(section => section.id === "soft-types");
  assert.ok(section);
  const text = JSON.stringify(section);
  assert.match(text, /one-sorted set theory/);
  assert.match(text, /∀ q, Rational\(q\) →/);
  assert.match(text, /∃ q, q ∈ ℚ ∧ P\(q\)/);
  assert.match(text, /∀ q, q ∈ ℚ → P\(q\)/);
  assert.match(text, /membership proof is visible/);
  assert.match(text, /unary soft type is defined exactly by membership/);
  assert.match(text, /Zero or multiple compatible notation interpretations produce an error/);
  assert.match(text, /what enters the kernel and exported proof/);
  assert.match(text, /one predicate-index lookup plus checked equivalence elimination/);
  assert.match(text, /not instance search or candidate enumeration/);
});

test("every tactic entry has a Gentzen-style rule schema", () => {
  for (const section of tacticGuideSections) {
    for (const entry of section.entries) {
      const rule = helpInferenceRule(entry.syntax);
      if ((section.id === "language" || section.kind === "language") && !["typecheck", "synthesize"].includes(entry.syntax)) {
        assert.equal(rule, undefined, `${entry.syntax} is explanatory, not a tactic rule`);
        continue;
      }
      assert.ok(rule, `${section.id}: ${entry.syntax} needs an inference rule`);
      const variants = rule.variants ?? [rule];
      assert.ok(variants.length);
      for (const variant of variants) {
        assert.ok(variant.label.trim());
        assert.ok(variant.conclusion.trim());
        assert.ok(Array.isArray(variant.premises));
      }
    }
  }
});

test("intro presents distinct implication and universal introduction rules", () => {
  const intro = helpInferenceRule("intro h");
  assert.equal(intro.variants.length, 2);
  assert.deepEqual(intro.variants.map(rule => rule.label), ["→I", "∀I"]);
  assert.match(intro.variants[0].premises[0], /Γ, h : P ⊢ Q/);
  assert.match(intro.variants[0].side, /discharges/);
  assert.match(intro.variants[1].conclusion, /∀ x, P\(x\)/);
  assert.match(intro.variants[1].side, /fresh/);
});

test("every displayed derivability judgment uses Γ for its local context", () => {
  for (const section of tacticGuideSections) {
    for (const entry of section.entries) {
      const inference = helpInferenceRule(entry.syntax);
      for (const variant of inference?.variants ?? (inference ? [inference] : [])) {
        for (const judgment of [...variant.premises, variant.conclusion]) {
          if (judgment.includes("⊢")) assert.match(judgment, /Γ/, `${entry.syntax}: ${judgment}`);
          assert.doesNotMatch(judgment, /\bcontext\b/i, `${entry.syntax}: ${judgment}`);
        }
      }
    }
  }
});

test("a named fact never masquerades as the whole derivation context", () => {
  for (const section of tacticGuideSections) {
    for (const entry of section.entries) {
      const inference = helpInferenceRule(entry.syntax);
      for (const variant of inference?.variants ?? (inference ? [inference] : [])) {
        for (const judgment of [...variant.premises, variant.conclusion]) {
          assert.doesNotMatch(judgment, /^\w+\s*:\s*[^,]+\s+⊢/, `${entry.syntax}: ${judgment}`);
        }
      }
    }
  }
});

test("Help examples receive safe Grace17 syntax highlighting", () => {
  const html = highlightGrace17('theorem demo (n : Nat)\n  shows n = 17\nproof\n  exact h -- checked');
  assert.match(html, /g17-keyword\">theorem/);
  assert.match(html, /g17-type\">Nat/);
  assert.match(html, /g17-number\">17/);
  assert.match(html, /g17-tactic\">exact/);
  assert.match(html, /g17-comment\">-- checked/);
  assert.doesNotMatch(highlightGrace17('<script>alert("x")<\/script>'), /<script>/);
  // A bare R, N, or Q is a variable unless it annotates a binder.
  assert.doesNotMatch(highlightGrace17("theorem t (A R C b : Set)\n  requires side : b ⊆ R"), /g17-type\">R/);
  assert.match(highlightGrace17("theorem t (x : R)\n  shows (0:R) = realZero"), /g17-type\">R/);
});

test("every built-in tactic spelling has semantic hover help", () => {
  for (const name of documentedTacticFamilies) {
    const entries = tacticHelpEntries(name);
    assert.ok(entries.length, `${name} needs hover help`);
    assert.ok(entries.every(entry => entry.summary && entry.detail));
  }
  assert.match(JSON.stringify(tacticHelpEntries("cases")), /Reason by cases/);
  assert.match(JSON.stringify(tacticHelpEntries("exfalso")), /contradiction/);
  assert.match(JSON.stringify(tacticHelpEntries("apply")), /backwards from its conclusion/);
});


test("declaration hovers distinguish construction mechanisms before checking", () => {
  const samples = [
    ["def f (x : Set) : Set := x", "def", "def"],
    ["def f (n : Nat) → Set\n  | zero => empty", "def", "def.recursive"],
    ["define f (n : Nat) → Set\n  | zero => empty", "define", "define"],
    ["defgraph g (A : Set) (x ∈ A) : A := x", "defgraph", "defgraph"],
    ["defchoose c (A : Set) (x ∈ A) := x = x", "defchoose", "defchoose"],
    ["defunique c (A : Set) (x ∈ A) := x = x", "defunique", "defunique"],
    ["predicate P (x : Set) := x = x", "predicate", "predicate"],
    ["class C (x : Set) := x = x", "class", "class"],
    ["datatype D(A : Set)\n  | leaf(value : A)", "datatype", "datatype"],
    ["def S (A : Set) : Set :=\n  {x ∈ A | x = x}", "def", "def.separation"],
    ["def S (A : Set) : Set := {{x} | x ∈ A}", "def", "def.replacement"],
    ["noncomputable transfinite def V (α : Ordinal) : Set", "transfinite", "transfinite"],
    ["noncomputable foundation def rank (x : Set) : Set", "foundation", "foundation"],
    ["noncomputable well-founded def f (A x : Set) : Set", "well-founded", "well-founded"],
    ['notation infixl 70 "⊗" => tensor', "notation", "notation"],
    ["instance named (x : Set)", "instance", "instance"],
    ["tactic finish(rule) := settle with $rule", "tactic", "tactic"],
  ];
  for (const [source, word, form] of samples) {
    const result = declarationHelpAtTextOffset(source, source.indexOf(word) + 1);
    assert.equal(result?.form, form, source);
    assert.equal(source.slice(result!.start, result!.end), word);
    assert.ok(result!.entry.summary && result!.entry.detail && result!.entry.example);
  }
  assert.equal(declarationHelpAtTextOffset("graphdef g (n : Nat) : Nat := n", 1), undefined);
  assert.equal(declarationHelpAtTextOffset("choosedef c (A : Set) (x ∈ A) := x = x", 1), undefined);
  const recursive = samples.find(sample => sample[2] === "well-founded")![0];
  assert.equal(declarationHelpAtTextOffset(recursive, 1)?.form, "well-founded");
  assert.equal(declarationHelpAtTextOffset(recursive, recursive.indexOf(" def") + 2)?.form, "well-founded");
  for (const source of ["-- defgraph g", '"defgraph g"', "theorem defgraph (x : Set)", "  exact defgraph"]) {
    assert.equal(declarationHelpAtTextOffset(source, source.indexOf("defgraph") + 1), undefined);
  }
  assert.equal(declarationHelpAtTextOffset(samples[3][0], samples[3][0].indexOf("(A") + 1), undefined);
  const app = readFileSync("workbench/app.js", "utf8");
  assert.match(app, /function symbolAtOffset\(offset\) \{\s*const imported = importSymbolAt\([^;]+;\s*if \(imported\) return imported;\s*const declaration = declarationHelpAtTextOffset/);
  assert.match(app, /kind: "declaration form"/);
});

test("the definition reference covers the trust and execution boundaries", () => {
  const definitions = tacticGuideSections.find(section => section.id === "definitions");
  assert.ok(definitions);
  assert.equal(definitions.kind, "language");
  const text = JSON.stringify(definitions);
  assert.match(text, /structural decrease/);
  assert.match(text, /wellFoundedOn/);
  assert.match(text, /not registered for ground evaluation/);
  assert.match(text, /No unbounded set comprehension/);
  const def = tacticGuideSections[0].entries.find(entry => entry.forms?.includes("def"));
  assert.match(def!.detail, /generates a checked name.type theorem/);
  const unique = tacticGuideSections[0].entries.find(entry => entry.forms?.includes("defunique"));
  assert.match(unique!.detail, /Uniqueness must be proved/);
  const choice = tacticGuideSections[0].entries.find(entry => entry.forms?.includes("defchoose"));
  assert.match(choice!.detail, /does not prove that the witness is unique/);
});

test("exact Help documents bounded goal-directed parameter inference", () => {
  const entry = tacticGuideSections.flatMap(section => section.entries).find(entry => entry.syntax === "exact fact");
  assert.ok(entry);
  assert.match(entry.detail, /from the goal, from the named premises in any order, and from uniquely matching local facts/);
  assert.match(entry.detail, /2048-match limit/);
  assert.match(entry.detail, /no unfolding or backtracking/);
});

test("words on module and import lines are module names, not types", () => {
  const html = highlightGrace17("module Grace.Cumulus.Nat\nimport Nat\nimport Set.Ordinal\ntheorem t (n : Nat)");
  assert.doesNotMatch(html.split("\n")[1], /g17-type/);
  assert.doesNotMatch(html.split("\n")[0], /g17-type/);
  assert.match(html.split("\n")[3], /g17-type/);
});
