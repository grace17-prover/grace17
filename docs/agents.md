# Grace17 for AI agents

This guide is for people building agents that prove theorems in Grace17, and
for the agents themselves. It describes the interfaces an agent can call, what
each returns, and a working loop that uses them well. If your agent changes
the Grace17 code base itself, read [AGENTS.md](../AGENTS.md) instead.

The contract is the same for an agent as for a person. A proof is admitted
only if the kernel checks it. Tactics, search, and suggestions are untrusted
conveniences, so nothing an agent produces can admit a false statement. What
an agent can do is explore quickly, read goal states, search the library, and
hand a human a checked result with its assumptions listed.

## Working with Claude Code

Grace17 ships a Claude Code skill: the write–check loop, the module header,
the proof style Cumulus expects, how theorem application infers its
parameters, and the elaborator pitfalls that cost the most time. There are
three ways to have it.

- **Inside this repository** nothing needs installing. The skill is at
  `.claude/skills/grace17-proving/`, and Claude Code run in a clone of the
  repository loads it when a task calls for it; `/grace17-proving` invokes it
  by hand.
- **In your own projects**, install it as a plugin from inside Claude Code:

  ```sh
  /plugin install grace17 --marketplace grace17-prover/grace17
  ```

  Older versions of Claude Code take it in two steps: `/plugin marketplace
  add grace17-prover/grace17`, then `/plugin install grace17@grace17`. The
  repository is its own marketplace (`.claude-plugin/marketplace.json`), and
  the plugin lives in `plugins/grace17`. Plugin skills are namespaced, so the
  skill answers to `/grace17:grace17-proving`. `/plugin marketplace update
  grace17` picks up new versions.
- **By hand**, copy `plugins/grace17/skills/grace17-proving/` into
  `~/.claude/skills/` to make it available everywhere without the plugin.

`python3 scripts/all-errors.py <file>` lists the first error of every theorem
in a module in one run, so an agent can plan its repairs instead of
discovering them one check at a time.

## The machine interface

Everything the Workbench shows is available as structured data with the
same semantics through the [machine interface](machine-interface.md):
`g17 serve` speaks newline-delimited JSON over stdio, and each method is
also a subcommand. The methods are `check` (per-theorem status, the goal
state after every step, diagnostics with positions, the partial trace on
failure, the axiom audit on request), `goal` (the state at a position),
`suggest` (`exact?`, `apply?`, or `rw?` at a position, each suggestion as
the command that pastes plus its theorem, instantiation, and evidence),
`search`, `declaration`, `audit`, `library`, and `notations`. An agent
that loops over check, goal, suggest, and paste should use it rather than
read printed text.

```sh
node bin/g17.ts check --json --module-root lib Probe.g17
node bin/g17.ts goal Probe.g17 --line 11 --column 12
node bin/g17.ts suggest Probe.g17 --line 12 --tactic 'exact?'
node bin/g17.ts search 'name:transitive module:Set.Core'
```

## Interfaces at a glance

| Interface | Use it for | Returns |
| --- | --- | --- |
| `g17 serve`, `g17 check --json`, `g17 goal`, `g17 suggest` | A tool or agent driving the checker | The Workbench's states, suggestions, search results, declarations, and audits as JSON; see [machine interface](machine-interface.md) |
| `g17 check --artifacts build/modules` | Checking files from a shell | Pass or fail; on failure the message, line, and the remaining goals with named hypotheses (`--json` adds the full tactic trace and every theorem's step states); with `--artifacts`, library imports replay from compiled artifacts in about a second |
| Workbench HTTP API, `POST /api/check` | Structured proof states | Every tactic's before and after goals, named hypotheses, search suggestions, `sorry` goals, statements, dependencies |
| TypeScript API, `checkWorkbenchFiles` | The same data in-process | The same structure, without a server |
| `g17 axiom-audit --json` | What a proof depends on | Named axioms, schema instances, Choice usage, dependency paths |
| Library search | Finding existing results | Qualified names, statements, source locations |
| `g17 export`, independent checkers | Handing off a certificate | A proof tape replayable by the Python, OCaml, and Rust checkers |

## The structured checking API

Start the Workbench server once; it also builds the browser bundle:

```sh
npm run workbench
```

Then post a workspace. Each file is a name and its full source. `activeFile`
selects which file's theorems are reported in detail; the others are context.

```sh
curl -s http://127.0.0.1:1717/api/check \
  -H 'content-type: application/json' \
  -d '{"files":[{"name":"Probe.g17","source":"module Probe\nimport Grace.Cumulus.Set.Core\n\ntheorem subset_chain (A B C : Set)\n  requires first : A ⊆ B\n  requires second : B ⊆ C\n  shows A ⊆ C\nproof\n  unfold Subset\n  intro x\n  intro hx\n"}],"activeFile":"Probe.g17"}'
```

The proof above stops one step short. The response says so and includes the
whole trace. Abridged to its last step:

```json
{
  "ok": false,
  "kind": "surface",
  "message": "1 goal remains; next is x ∈ C",
  "line": 11,
  "trace": {
    "steps": [
      {
        "line": 11,
        "command": "intro hx",
        "after": {
          "goals": [
            {
              "goal": "x ∈ C",
              "assumptions": ["A ⊆ B", "B ⊆ C", "x ∈ A"],
              "locals": [
                { "name": "first",  "formula": "A ⊆ B" },
                { "name": "second", "formula": "B ⊆ C" },
                { "name": "hx",     "formula": "x ∈ A" }
              ]
            }
          ]
        }
      }
    ]
  }
}
```

Three fields matter most. `goal` is the formula to prove. `locals` are the
hypotheses by name, which is what you cite in `exact ... with first, hx`.
`assumptions` are the same formulas without names, in context order.

When a file checks, the response has `ok: true` and a `theorems` array. Each
theorem carries its `statement`, its `steps` with the same before and after
states, its `sorries`, and its `dependencies` (axioms, theorems, definitions).

The same function is available in-process, which is faster for many calls:

```ts
import { checkWorkbenchFiles, workbenchFailure } from "./src/index.ts";

let result;
try {
  result = checkWorkbenchFiles(files, "ZFG", ["Probe.g17"], { includeKernelDetails: false });
} catch (error) {
  result = workbenchFailure(error);   // same shape as the HTTP failure response
}
```

The HTTP server fixes the foundation to ZFG. The in-process call and the
command line accept `ZF`, `ZFC`, or `ZFG`.

## Use `sorry` as a probe

A proof that ends in `sorry` checks successfully, so you get the complete
step trace and a `sorries` entry recording what remains:

```json
"sorries": [
  { "theorem": "Probe.subset_chain", "line": 12, "goal": "x ∈ C",
    "axiom": "sorry.Probe.subset_chain.12.1" }
]
```

This is the most useful pattern for an agent: write the steps you are sure
of, end with `sorry`, read the remaining goal with its hypotheses, and
continue. A `sorry` introduces a named axiom, so it also appears in the axiom
audit and in `dependencies.axioms`. Cumulus accepts nothing that contains a
`sorry`.

## Query tactics return commands you can paste

`exact?`, `apply?`, and `rw?` run bounded, deterministic search over the
imported environment. Their results appear in the step's `info` field as
fully qualified commands:

```json
{
  "command": "apply?",
  "info": {
    "title": "apply?",
    "items": [
      "apply Grace.Cumulus.Set.Core.powerset.membership_iff.forward at A, C",
      "apply Grace.Cumulus.Set.Basic.Set.Subset.equation.backward at A, C"
    ]
  }
}
```

Replace the query tactic with the suggested line. A finished proof should
not contain `?` tactics. The written form is faster to replay, stable when
the library grows, and readable by the person who reviews it. When search
finds nothing, the message says so; search the library yourself or prove the
missing lemma.

## Finding theorems

Three complementary routes:

- **Library search.** `g17 search 'name:mul module:Complex'` runs the
  Workbench's search from the shell, and the `search` method of the machine
  interface runs it over the protocol. It matches words in names,
  statements, and section context, with `name:`, `module:`, `kind:`,
  `symbol:`, `conclusion:`, and `pattern:` criteria; see [library search](library-search.md)
  for the syntax. In-process, the index is `src/library-search.ts`:
  construct `new LibrarySearchWorkspace(files)` over a map of file path to
  source and call `workspace.index.search(query)`;
  `scripts/benchmark-library-search.ts` is a complete example.
- **Grep the source.** Cumulus is plain text under `lib/Grace/Cumulus/`.
  Names are dotted and descriptive: `Subset.transitive`, `Zorn.theorem`,
  `FTC.derivative_of_integral`. Searching for the statement's key symbols or
  for the subject's namespace usually lands in the right module.
- **The guide.** [cumulus.md](cumulus.md) lists what each module provides
  and which entry point to import for a subject.

Prefer applying an existing theorem to re-proving it. If a lemma is missing,
add it to the module where it belongs. Do not inline it in your proof.

## A working loop

1. **State the theorem first.** Write `requires` hypotheses with names and a
   `shows` clause. Check the file with the proof body `sorry`. If the
   statement does not elaborate, the message names the line and the problem,
   usually a missing import or an unresolved name.
2. **Read the goal.** From the `sorries` entry or the trace, take the goal and
   the named locals.
3. **Try automation on the goal.** `ring` for polynomial identities,
   `decide` for closed statements about finite sets (membership, inclusion,
   equality, cardinality over set literals),
   `linarith` for linear inequalities over the reals and rationals (products are atoms, so
   state nonlinear facts such as `0 ≤ x * y` as hypotheses first), `arith`
   for linear arithmetic over naturals, `simp [rules]` for rewriting,
   definitional and logical closing, and membership in compound sets
   (the membership lemmas and `Subset` are automatic), `typecheck` for
   carrier obligations. See [tactics](tactics.md). A tactic that fails costs
   nothing but time.
4. **Decompose.** `unfold` a definition, `intro` binders and premises,
   `obtain ⟨x, hx⟩ := h` for existentials, `cases` for disjunctions,
   `have h : P` for an intermediate fact. Re-check after each step and read
   the new goal.
5. **Apply library results.** Use `apply?` or search to find a candidate,
   then write it out: `exact Subset.transitive with first, second`,
   or `have h := theorem at args with premises`.
6. **Finish and audit.** Remove every `sorry` and `?`. Run the axiom audit
   and check that Choice appears only if it is needed. Check under `ZF` if
   the subject permits.

Checking the probe file above from the command line takes about half a
second. Files that import large subjects such as real analysis take longer,
because their imports are elaborated too; the in-process API keeps a loaded
workspace between calls.

## Foundations and the axiom audit

The command line accepts `--foundation ZF`, `ZFC`, or `ZFG`. A theorem checked
under ZFG may still have a Choice-free proof; the audit tells you:

```sh
node bin/g17.ts axiom-audit --json --foundation ZF --module-root lib Probe.g17 --theorem Probe.subset_chain
```

The report lists direct and hereditary named axioms, schema instances
(Separation, Replacement, datatypes, recursion), classical double-negation
use, and a dependency path to each axiom. An incomplete audit exits with
status 1 and cannot certify the absence of Choice. See
[axiom audits](axiom-audit.md).

## Handing off a result

Before presenting a theorem as done:

- the file checks with no `sorry` and no query tactics;
- the axiom audit is complete and its Choice usage is stated;
- you have read the statement as mathematics. The kernel guarantees the
  proof; whether the statement says what you meant is your call;
- optionally, the certificate has been exported and replayed by an
  independent checker:

```sh
node bin/g17.ts compile --module-root lib Probe.g17 --out probe.g17m --environment probe.g17env
python3 checkers/python/g17check.py probe.g17m --environment probe.g17env
```

Report which of these you ran. A human takes ownership of anything
submitted to Cumulus; see [CONTRIBUTING.md](../CONTRIBUTING.md).

## Known limitations

These are the gaps most likely to matter to an agent builder today:

- The HTTP server checks under ZFG only; `g17 serve` and the subcommands
  accept a `foundation`.
- Query-tactic search is bounded. In the example above, `exact?` did not find
  `Subset.transitive` for the goal `A ⊆ C` from `A ⊆ B` and `B ⊆ C`, while
  `exact Subset.transitive with *` closes it in one line. When search fails,
  name the theorem yourself.
- `linarith` interprets only addition, subtraction, and negation over the
  reals and rationals; products are atoms. Nonlinear facts such as `0 ≤ x * y` must be
  stated as hypotheses (for example from `realMulValue.nonnegative`) before
  the linear step.

## Pitfalls that cost an agent iterations

The checker's message is quoted for each so it can be matched.

- **`apply thm at args` leaves carrier guards first.** The goals after
  `apply` are `A ∈ Real`, `B ∈ Real`, then the premise, so a following
  `intro` fails with "intro requires a universal or implication goal".
  Prefer `have h : P by tactic` for the premise, then `exact thm with h`;
  the `at` list is only needed when the goal and the named premises leave a
  parameter undetermined.
- **A negated lemma does not apply itself.** `exact realLe.not_less at A, B
  with *` establishes `¬(B < A)` but the goal is `⊥`: list the contradicting
  fact after the premises, `with *{2}, le, lt`. The message is "proof
  establishes ¬..., but the goal is ⊥".
- **A contradiction branch starts with `exfalso`.** "proof establishes ⊥,
  but the goal is ∃ ..." means the goal was never changed to `⊥`.
- **Numerals in set comprehensions default to `Nat`.** Write
  `{ T ∈ ℝ | (0:R) ≤ (T:R) ∧ (T:R) * (T:R) ≤ X }`; the message is "cannot
  resolve notation ≤ for operand types Nat, ?". In a real statement, `-1` has
  to be written `-(1:R)` for the same reason.
- **`unfold` also rewrites with local equalities.** After `unfold f`, a
  following `rw h` can fail with "rewrite rule does not match" because the
  goal is already in the rewritten form; close with `cc` instead.
- **Two soft-typed operands may not resolve notation.** For
  `(X Y : NonnegativeReal)`, `X ≤ Y` fails with "cannot resolve notation ≤
  for operand types NonnegativeReal|Real, NonnegativeReal", and `(X:R)` is
  rejected because `X` "already has type NonnegativeReal". Take
  `(X Y : Real)` and `requires nonnegativeX : NonnegativeReal(X)`.
- **`defunique` binders are `Set`, `Nat`, or `Real` only.** Hypotheses go in
  `requires`; a `def` that wraps the value with a declared result type then
  needs an attached `proof` block for its `.type` obligation.
- **Generated names can collide.** `defunique f` publishes `f.exists`,
  `f.unique`, and `f.selected`; a theorem named `f.exists` nearby fails
  with "Duplicate proposition name" reported at the `defunique` line.
- **`with *` only looks at local facts.** It will not fetch a library theorem
  or prove `t = t` for you. Bind `have one := realZero.lt_one` or
  `have same : T * T = T * T` with `rfl` first, or name the premise.
- **Destructure predicates directly.** The style gate rejects `unfold P at h`
  followed by `rcases h with ...` ("recursive destructuring follows
  transparent predicates directly"); write `rcases h with ...` alone.
- **`with *` already fills declared `requires` premises.** Listing one again,
  `lemma at a, b with *, different`, fails with "has no remaining argument at
  different". Name a premise after the star only for an implication inside
  the conclusion, as in `with *, positive` for `shows 0 < n → …`.
- **`?_` takes the whole remaining proposition.** In
  `refine ⟨w, h, ?_, ?_⟩` against `∃ z, A ∧ (B ∧ C)`, the first `?_` captures
  `B ∧ C` and the message is "refine has 1 unused constructor entry". Use
  `_` for leaf holes when several goals are wanted.
- **`rw` does not rewrite under a binder.** With `equal : y = x` and a goal
  `∀ q, …` or `∃ zs, …`, the message is "rewrite rule does not match";
  `intros` or `refine` first, then rewrite inside the component.
- **Nat `arith` needs a comparison goal.** After `exfalso` it reports "arith
  requires a linear equality or comparison goal". Derive `have bad : p < p`
  by `arith` and finish with `Less.irreflexive at p with *, bad`.
- **Nat `arith` proves comparisons more readily than equalities.** When
  "arith found no supported linear arithmetic step" appears on an equality
  goal, prove `x ≤ 0` (or both directions) by `arith` and finish with
  `LessEqual.antisymmetric`.
- **Nat `ring` carries numeral coefficients.** `2 * (q * q) = q * q + q * q`
  and `(4 * a + 2) * (a + 1) = 4 * a * a + 6 * a + 2` are ring identities;
  a normal form writes each monomial as `coefficient * product`, so a
  `ring_nf` result reads `4 * (x * y)` rather than four copies.
- **Successor injectivity is a generated law.** Nat `arith` does not derive
  `k = c` from `succ(k) = succ(c)`; use `Naturals.injective.succ at k, c with h`.
- **A bounded existential takes only the first disjunct.** `∃ S ∈ X, P ∨ Q`
  parses as `(∃ S ∈ X, P) ∨ Q`; write `∃ S ∈ X, (P ∨ Q)`.
- **A natural embedded in ℝ needs its carrier in statements.** `realNat(k) + 1`
  in a theorem statement fails with "cannot resolve notation + for operand
  types Set, Nat"; write `(realNat(k):R) + 1`. After `rw realNat.succ` the goal
  shows `realAddValue(…)`, which `linarith` and `ring` read but `rw` with a
  `+` fact does not; restate the law in operator form once.
