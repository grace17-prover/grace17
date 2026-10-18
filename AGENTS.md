# Working on Grace17 with a coding agent

This file is for AI coding agents operating in this repository, and for the
people directing them. Read [CONTRIBUTING.md](CONTRIBUTING.md) first: the
human directing you is the author of record for anything you produce, and
the rules there apply to your output.

If your task is to prove theorems in Grace17 rather than to change it, read
[docs/agents.md](docs/agents.md): it documents the structured checking API,
goal states, search, and a working loop. The
[machine interface](docs/machine-interface.md) is the JSON protocol behind
`g17 serve`, `g17 check --json`, `g17 goal`, `g17 suggest`, and
`g17 search`: use it instead of parsing printed output.

## What this repository is

Grace17 is a proof assistant for mathematics based on ZF set theory. The
kernel, elaborator, tactics, and proof machine are TypeScript in `src/`. The
mathematics library, Cumulus, is `.g17` source under `lib/Grace/Cumulus/`.
Independent checkers in `checkers/python/`, `checkers/ocaml/`, and
`checkers/rust/` replay
exported proof certificates without sharing code with the kernel.

Read these before making changes:

- [docs/architecture.md](docs/architecture.md): how the system fits together
- [docs/kernel-format.md](docs/kernel-format.md): the normative checker contract
- [docs/proving.md](docs/proving.md) and [docs/tactics.md](docs/tactics.md): how proofs are written, and the tactic reference
- [docs/cumulus.md](docs/cumulus.md): what is in the library and what to import
- [docs/soundness.md](docs/soundness.md): what is trusted

## Commands

Node.js 24 or later. Run `npm ci` once.

| Task | Command |
| --- | --- |
| Check one file | `node bin/g17.ts check --module-root lib path/to/File.g17` |
| Check under ZF only | add `--foundation ZF` |
| Check all of Cumulus | `npm run check:cumulus` |
| Check all of Cumulus, continuing past failures | `npm run check:cumulus -- --continue` |
| Axiom audit for a theorem | `node bin/g17.ts axiom-audit --module-root lib File.g17 --theorem Full.Name` |
| Goal at a position, as JSON | `node bin/g17.ts goal --module-root lib File.g17 --line N --column C` |
| Query tactic at a position, as JSON | `node bin/g17.ts suggest --module-root lib File.g17 --line N --tactic 'exact?'` |
| Library search | `node bin/g17.ts search 'name:transitive module:Set.Core'` |
| The JSON protocol over stdio | `node bin/g17.ts serve` (see [docs/machine-interface.md](docs/machine-interface.md)) |
| One test file | `node --test tests/name.test.ts` |
| Full suite (slow) | `npm test` |
| Cumulus header check | `npm run check:headers` |
| Conformance, TypeScript and Python | `npm run conformance && npm run conformance:python` |
| OCaml checker, if installed | `npm run test:ocaml` |
| Rust checker, if installed | `npm run test:rust` |
| Regenerate the Top 100 page | `npm run docs:top100` |
| Verify introduction excerpts | `npm run docs:introduction:check` |
| Browser bundle and Workbench | `npm run workbench` |

Checker output is JSON with `--json`: every theorem's status and the goal
state after each step, and on failure a diagnostic with its position and
the partial trace. Error messages carry source line numbers. A `settle` or
`exact` failure reports the goal that remains.

## Rules

**The trusted boundary is not yours to move.** Do not add kernel rules,
axioms, foundation profiles, trusted evaluation shortcuts, or changes to the
G17M or G17C formats. If a task seems to require one, stop and report that to
the human. Tactics in `src/` are untrusted and may be extended freely as long
as they produce certificates the kernel checks.

**Never make a test pass by editing its expectation.** Conformance vectors,
fixtures, digests, and environment hashes are evidence. If one looks wrong,
say so and stop.

**No admissions in Cumulus.** Do not leave `sorry` in `lib/`. Report a
theorem you cannot finish as unfinished.

**Prefer ZF.** Check new mathematics with `--foundation ZF` when the subject
permits. If a proof needs Choice, say so and make sure the axiom audit shows
it.

**Match the library's style.** Use the file header from CONTRIBUTING.md.
Follow the naming and namespace conventions of the module you are editing.
A bundled structure keeps the plain noun (`Group(G)`, `CommRing(R)`,
`Ideal(R, I)`); the predicate over separate pieces carries an `Is` prefix
(`IsGroup(A, op, unit, inv)`, `IsCommRing(A, add, zero, neg, mul, one)`,
`IsIdeal(A, add, zero, neg, mul, I)`), and so do its lemmas
(`IsCommRing.mul_comm`).
Prefer named hypotheses, `have` with stated propositions, `calc`, and
sections over long tactic runs. The style test rejects mechanical verbosity.

**Documentation is timeless and impersonal.** Describe the system as it is.
Do not write version numbers, dates, checkpoint names, validation logs, or
narration of your own session ("the browser permission was declined", "the
owner must decide"). Do not describe what you tried. If a document needs to
record that something is not yet done, say what is missing in one sentence.

**Do not commit build outputs.** `build/`, `workbench/generated/`, and
`workbench/service-worker.js` are generated. `node_modules/` is installed.

**Keep the Python checker dependency-free.** It must run with a bare Python 3.
The Rust checker depends only on `num-bigint`, `sha2`, and `serde_json`.
A checker shortcut that names a library definition (`Grace.Core.Nat.Rec.predecessor`)
must be updated in the runtime and in all three checkers together.

## Working on a proof

1. State the theorem with named `requires` hypotheses and a `shows` clause.
   Check the statement reads as the intended mathematics before proving it.
2. Run the checker on the file. Read the remaining goal.
3. Use `exact?`, `apply?`, and `rw?` for bounded search, and the Workbench
   library search or `grep` over `lib/` to find existing results.
4. Prefer applying existing Cumulus theorems to re-proving them. If a lemma is
   missing, add it in the module where it belongs rather than inline in your
   proof.
5. When the file checks, run the axiom audit and the relevant tests.

## Before you finish

Run the checks that apply to what you changed, and report which ones you ran
and their results. Do not report a check you did not run. Summarize
what changed in plain language for the human who will review and sign off
the work. They are the author; make it easy for them to stand behind it.
