---
name: grace17-proving
description: Write and check Grace17 proofs and Cumulus modules — module headers, the check loop over the JSON machine interface, reading goal states, asking for suggestions, tactics that work, and the elaborator pitfalls that cost the most time.
---

# Proving in Grace17

Grace17 is a proof assistant for set-theoretic mathematics. A proof counts
only when the kernel checks it; everything an agent writes is checked from
the ZF(C) axioms, so iterate freely. The library is Cumulus, under
`lib/Grace/Cumulus/`. The full agent guide is `docs/agents.md`; the tactic
reference is `docs/tactics.md`; the JSON interface is
`docs/machine-interface.md`; this skill is the working loop.

Run every command from the repository root with
`node --disable-warning=ExperimentalWarning bin/g17.ts …` (written `g17 …`
below). Every method subcommand prints JSON (`--text` gives the readable
form of `search` and `goal`); read results as JSON, do not scrape printed
text. A method subcommand prints the envelope `{"ok", "version",
"method", "result"}` and the fields named below are in `result`;
`check --json` alone prints its fields at the top level. `g17 --help`
prints the usage.

## The loop

1. Inventory before writing: `g17 search 'name:<word> module:<Area>'`
   (the Workbench query language: `name:`, `module:`, `kind:`, `symbol:`,
   `conclusion:`, `pattern:`; see `docs/library-search.md`). A
   `conclusion:` value runs to the next filter and may hold wildcards,
   `g17 search 'conclusion: _ = 0 ∨ _ = 0'`; `name:mul_eq_zero` matches
   the pieces `mul`, `eq`, `zero` of a name. Then
   `g17 declaration <Name> --module <Module>` for a statement (a name
   outside the loaded closure answers with `inScope: false` and the
   `import` to add; a generated name such as
   `Bool.inductive.disjoint.false.true` or a defgraph's `ident.value`
   resolves too; `--module` picks among same-named declarations, and an
   `ambiguous_name` error lists `declarations` with their modules; a
   theorem named like a generated property answers with the theorem and
   the property it hides in `shadows`), and
   `g17 library --area <Area>` for a module's declarations.
   `g17 closure <Module>` lists a module's import closure in dependency
   order with each module marked `choiceFree`, and `--from <Module>` the
   import chain to a dependency, so "what loads under ZF" has a direct
   answer. Before writing
   `theorem at a, b with h1, h2`, ask `g17 signature <Name> --file <file>`:
   it lists `parameters` and `premises` in the order the `at` and `with`
   lists supply them, section variables and hypotheses first, from the
   header alone, so it works while the file still fails (a generated
   theorem such as `ident.closed` answers from its statement, with
   `generated: true`). Do not duplicate deep material; build on what
   exists.
2. Write the module. A library file is

   ```g17
   -- One or two lines saying what the module proves
   -- Part of Cumulus, the Grace17 mathematics library.
   -- Copyright (c) 2026 Grant Passmore.
   -- Released under the Apache License 2.0. See LICENSE in the repository root.
   -- Authors: Grant Passmore

   module Grace.Cumulus.Real.FiniteSum
   import Analysis.Sequences
   import Power

   theorem realPartialSum.succ (u : Set, n : Nat)
     shows realPartialSum(u, succ(n)) = realAddValue(realPartialSum(u, n), uₙ)
   proof
     rw realPartialSum
   ```

   The `module` line names the module its path denotes
   (`lib/Grace/Cumulus/Real/FiniteSum.g17` is `Grace.Cumulus.Real.FiniteSum`);
   Cumulus writes the qualified name, and the bare `module FiniteSum` means the
   same. The module's namespace is implicit and exported. Imports are read relative
   to the module, innermost first: `import Power` finds `Grace.Cumulus.Real.Power`,
   `import Nat.Subtraction` finds `Grace.Cumulus.Nat.Subtraction`. Imported
   declarations are usable by short name and as `Module.name`. At most three
   imports per module (root modules excepted); Unicode symbols (∀ ∃ ∈ ⊆ ∧ ∨ ¬ →);
   lines under 80 columns where practical.
3. Check it: `g17 check --json --module-root lib <file>`. The result has
   `status` (`checked` or `failed`), `theorems` (each with `status`
   `proved`, `admitted`, or `failed`, and the goal state after every step),
   and `diagnostics` (each with `file`, `line`, `column`, `message`, and the
   `theorem` it falls in). On failure the theorems that completed before
   the failure are reported as usual and the failed theorem carries the
   partial trace up to the failing step; that step's `after` is the state
   where the proof stopped. The JSON is on standard output whether or not
   the file checks (the exit status says), so `> out.json` captures it.
   A `defgraph`'s codomain proof is a proof block like a theorem's, named
   `ident.closed`. `python3 scripts/all-errors.py <file>` lists the
   first error of every theorem in one run; `g17 check --continue` goes on
   past a failing module and lists every failure at the end (`--quiet`
   prints the failures and the summary alone). `g17 check --imports`
   adds a `note` diagnostic for every declaration the module uses only
   through a transitive import, with the `module` to import directly:
   add that import, so an unrelated module dropping its own does not
   break yours. A `warning` of kind `shadowed-property` says a theorem
   restates a generated property under the same name; rename it.
4. Read the goal where you are: `g17 goal --module-root lib <file> --line N
   --column C` returns `state.goals`, each with `goal` and `locals` (name
   and formula), as the Workbench goal pane shows them. It answers in a
   failing file too: in an earlier theorem that completed, or in the
   failing theorem up to its failed step; past that step it says
   `code: "after_failure"` with the state where the proof stopped (and
   `suggest` answers the error `after_failure`), so fix that step first.
   Write `sorry` where a proof is unfinished to see the goal there as a
   warning. To see what a written term or formula means where the module
   reads it, `g17 elaborate '<text>' --file <file> --line N` (or
   `--module <Module>`, with `--variables '(x : Set)'` for free variables)
   prints its kernel form as the goal pane prints it and with full names.
5. Ask for suggestions before guessing a lemma name: `g17 suggest
   --module-root lib <file> --line N --tactic 'exact?'` (or `apply?`,
   `rw?`) runs the query tactic at that position without editing the file.
   Each suggestion has `command` (the line that pastes), `name` (the full
   theorem name), `arguments`, `premises` with their `evidence`, and
   `closes`. Paste `suggestions[0].command` at `inserted.line` with the
   indentation of `inserted.text`; a finished proof contains no `?` tactic.
6. Fix, recheck, repeat. When the module checks, add `import <Name>` to the
   area's root module (`lib/Grace/Cumulus/<Area>.g17`), run
   `npm run -s check:cumulus` (the whole library; look for `surface error` and
   `admitted with sorry`), `node scripts/shorten-proofs.ts --write --root lib <file>`
   to apply the standard simplifications, and the tests that touch the
   library: `node scripts/run-tests.ts cumulus-style site-integration`.
7. Before handing off: `g17 check --json --audit --module-root lib <file>`
   adds each theorem's axiom audit in one run (a one-shot `g17 audit` loads
   the environment every time; several `--theorem` options share one load
   and answer `audits`, one entry per name, with an `error` entry for a
   name the environment does not hold);
   state whether Choice appears.

For many calls on one file, keep one `g17 serve` process open and send one
JSON request per line (`{"id": 1, "method": "check", "params":
{"files": [{"name": "Probe.g17", "source": "…"}]}}`); it keeps the checked
imports in memory, and the methods and shapes are the same. On a deep
closure a one-shot call spends tens of seconds loading the environment;
in `serve` the second request on the same files answers in milliseconds,
whichever method. The fast loop in `docs/machine-interface.md` is ten
lines of shell or Node that keep one `serve` and pipe requests through
it. `g17 serve --pin` keeps the dependency sources it first read while
other agents edit them.

Example of the loop on a proof that ends in `sorry`:

```sh
g17 check --json --module-root lib Probe.g17      # status checked, admitted
g17 goal --module-root lib Probe.g17 --line 10    # goal: f(Xₖ) ∈ B
g17 suggest --module-root lib Probe.g17 --line 10 --tactic 'exact?'
#  suggestions[0].command =
#  "exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)"
#  → replace the sorry line with it
g17 check --json --audit --module-root lib Probe.g17   # status proved
```

## Proof style

Readable, stepwise proofs: name the facts you use (`have bound := realPartialSum.term_le_prefix with sequence`),
then close with `exact`, `linarith`, `ring`, or `simp`. A proof should not be
much longer than the same proof in a comparable system. No `sorry` in
Cumulus. Theorem names are dotted and descriptive (`Subset.transitive`,
`realPartialSum.zero_terms`).

## Applying theorems

- `have h := theorem with hyp1, hyp2` names the premises; parameters are
  inferred from them. `have h := theorem with *` fills every premise from
  unique local matches; `exact theorem with *` also matches the conclusion
  against the goal. Write `theorem at a, b with …` only when a parameter
  appears in the conclusion alone, or two local facts match one premise.
- Equivalences: `h.forward`, `h.backward`; conjunctions: `h.left`, `h.right`
  (bind the fact first; `(theorem with …).left` is not allowed).
- Destructure directly: `obtain ⟨k, hk, eq⟩ := le` sees through a defined
  predicate; no `unfold` first.
- Nested-binder facts apply one binder at a time: `have first := f with hx`
  then `exact first with hy, same`.

## Pitfalls that cost time

- `rw` works only under a single binder; for `∀ i ∈ n, …` goals, `intros i hi` first.
- Parenthesize quantified formulas inside connectives: `P ∧ (∃ j ∈ n, A ∨ B)`.
- Facts proved before `induction m` are not visible in the branches; re-derive them inside each branch.
- A bound variable from `∀ k ∈ m` with `m : Nat` needs `have kNat := natural.member at m with hk` before it is used as a natural.
- With real notation in scope write `(0:R)`, `(1:R)`, `(0:N)`, and casts `(t:R)`. `arith` is for naturals (no `≠`, no equalities); `linarith` and `ring` are for reals and need the atoms' realness in context (`have xReal := … ∈ ℝ`).
- `realAddValue(a, b)` and `a + b` are different terms. `linarith` bridges them when `a`, `b` are non-literal reals with realness facts; keep `u(j) = 0` as a hypothesis rather than rewriting it into the goal.
- A `def` with literal `1` means `realOne`; before rewriting with such a definition prove `have same : f(args) = body` by `unfold f; rfl`.
- Never state a lemma of the shape `requires P(bigger(T)) shows P(T)` (for example `0 < realMax(0, T) → 0 < T`): the refinement search behind `with *` loops on it and unrelated modules fail. Inline the case split instead.
- A typed parameter `(C : Real)` given a set term needs that term's realness in context before the application.
- Query-tactic search is bounded: `exact?` may miss a theorem that
  `exact Subset.transitive with *` applies in one line. When `suggest`
  returns nothing, `g17 search` for the statement's symbols and name the
  theorem yourself.

## Where things are

- Reals: `Real/*` (Dedekind reals, `Real/FiniteSum`, `Real/Power`, `Real/Analysis/*`).
- Sets, relations, functions, ordinals, cardinals: `Set/*`, `Relation/*`, `Cardinal/*`.
- Fixed points and game theory: `FixedPoint/*` (Kuhn, Brouwer), `GameTheory/*` (Nash).
- The Top 100 catalogue: `docs/top-100.json`, regenerated with `npm run -s docs:top100`.
