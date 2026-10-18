# Contributing to Grace17

Thank you for your interest in Grace17. This guide explains how the project
works, what kinds of contributions are most useful, and the conventions that
keep the library coherent. If something here is unclear, open an issue and
ask; questions are contributions too. Please remember that Grace17 is my
personal research project, and my goals may be different from yours.

## Ways to contribute

- **Mathematics in Cumulus.** New results, better proofs of existing results,
  and new subjects. Small is fine. A well-chosen lemma with a readable proof
  is more valuable than a large development nobody can follow.
- **Awkward proofs.** If a proof was harder than it should have been, open an
  issue with the file. These examples drive the automation and ergonomics
  work more than anything else.
- **Automation and tactics.** Tactics are untrusted and the kernel checks
  what they produce, so you can experiment without risking soundness.
- **Documentation.** Corrections, missing explanations, and examples.
- **Checkers.** An independent checker in a new language, or attacks on the
  existing ones. Soundness reports take priority over everything else.
- **Bug reports.** With the smallest reproduction you can manage.

## Getting set up

You need Node.js 24 or later. Python 3 is needed for the independent Python
checker, OCaml 5 with Zarith for the OCaml checker, and a Rust toolchain for
the Rust checker.

```sh
git clone https://github.com/grace17-prover/grace17.git
cd grace17
npm ci
npm test
npm run workbench
```

`npm test` checks the Cumulus file headers, builds the browser bundle, and
runs the full suite, one process per file. Library imports in tests come
from a module store under `build/test-store`, built on first use and reused
while the sources are unchanged, so a file that imports a large closure
loads it in well under a second; `scripts/run-tests.ts --from-source`
elaborates the library instead, as `node --test` on a single file does.
During development, run a single file:

```sh
node scripts/run-tests.ts cumulus
node --test tests/cumulus.test.ts
node bin/g17.ts check --module-root lib lib/Grace/Cumulus/Set/Zorn.g17
```

The [architecture guide](docs/architecture.md) describes how the system fits
together. The [docs index](docs/README.md) lists everything else.

## Repository layout

| Path | What lives there |
| --- | --- |
| `src/` | Kernel, elaborator, tactics, proof machine, Workbench backend |
| `lib/Grace/Cumulus/` | The mathematics library |
| `lib/Grace/Core/`, `lib/Grace/Bootstrap/` | Computation bootstrap and ZF foundation layer |
| `examples/` | Small checked files, one per subject |
| `checkers/` | Independent Python, OCaml, and Rust checkers |
| `conformance/` | Language-neutral accept and reject vectors for every proof rule |
| `workbench/` | Browser proof assistant |
| `scripts/` | Build, benchmark, and documentation tooling |
| `tests/` | Test suite |
| `docs/` | Documentation |

## Writing mathematics in Cumulus

**Modules and namespaces.** One module per file. The file opens with its
qualified name, `module Grace.Cumulus.Real.FiniteSum`, which must agree with
its place under `lib/` (the bare `module FiniteSum` is accepted too and means
the same). The module's declarations live in its own namespace, which
importers see without qualification, and `import` names are read relative to
the importing module (`import Real.FiniteSum` from anywhere under
`Grace.Cumulus`, `import Sequences` from a sibling). Names are dotted
and descriptive: `Subset.transitive`, `Zorn.theorem`,
`FTC.derivative_of_integral`. Follow the existing pattern in the module you
are extending.

**Prove in ZF when you can.** Cumulus distinguishes results that need Choice
from those that do not. Use `node bin/g17.ts axiom-audit` to see what your
proof depends on, and prefer the weakest foundation that works. The
[axiom audit guide](docs/axiom-audit.md) explains the report.

**No admissions.** Cumulus contains no `sorry`. A pull request that adds one
will not be merged, though a draft with `sorry` placeholders is a fine way to
discuss a proof plan in an issue.

**Readable proofs.** Prefer named hypotheses, `have` with a clear statement,
and `calc` chains over long runs of low-level steps. Use sections for shared
context. The style test in `tests/cumulus-style.test.ts` rejects mechanical
verbosity such as repeated `assumption` runs; if it fails, there is usually a
cleaner proof.

**Examples.** If you add a subject, add a short starter file in `examples/`
that shows how to use it. These are the first thing new users read.

**Top 100.** If your work completes or extends an entry in the
[Top 100 catalogue](docs/top-100.md), update `docs/top-100.json` and run
`npm run docs:top100`.

## Changing the kernel or the checkers

The trusted boundary is the kernel in `src/`, the proof machine, the
independent checkers, the ground evaluator, and the formats specified in
[docs/kernel-format.md](docs/kernel-format.md). Changes there need more care
than changes anywhere else:

- Open an issue first and describe the change and why it is needed. Adding a
  rule, an axiom, or a trusted shortcut is a design decision.
- Every new rule or side condition needs a positive and a negative
  conformance vector, and all four implementations must agree on them.
- Do not edit conformance vectors, fixtures, or digests to make a test pass.
  If a vector is wrong, say so in the pull request and explain why.
- The Python checker has no dependencies. Keep it that way.
- Run `npm run conformance`, `npm run conformance:python`, and, if you have
  the toolchains, `npm run test:ocaml` and `npm run test:rust`.

If you think you have found a soundness bug, open an issue immediately with
the reproduction. See [docs/soundness.md](docs/soundness.md).

## Pull requests

- Keep each pull request to one topic. Several small requests are easier to
  review than one large one.
- Explain what the change does and why. For mathematics, say what is proved
  and under which foundation.
- Run the relevant checks before opening the request, and say which you ran.
- Sign off your commits with `git commit -s`. This adds a `Signed-off-by`
  line certifying the [Developer Certificate of Origin](https://developercertificate.org/):
  that you wrote the contribution or have the right to submit it under the
  project license.
- Expect questions. Review is a conversation about the mathematics and the
  code.

## AI-assisted contributions

AI tools are welcome in this project. Grace17 is designed for people and
agents to work on the same checked mathematics, and the kernel does not care
who wrote a proof. The rules below exist so that review stays meaningful and
the library stays readable.

1. **A human author owns every contribution.** You are the author of what you
   submit. You must understand it, be able to explain any line of it, and be
   prepared to maintain it. "The model wrote it" does not answer a review
   question.
2. **Disclose tool use.** Say in the pull request description that AI
   assistance was used and roughly how: drafting proofs, searching the
   library, writing documentation, and so on. It helps reviewers know where
   to look.
3. **Checked is not the same as right.** The kernel guarantees that a proof
   is valid. Whether the statement says what you meant is your judgment, as
   are the definitions and the choice of hypotheses. Read every
   statement you submit as if it were in a paper with your name on it.
4. **Run the checks yourself.** Do not submit output you have not run through
   the test suite on your own machine.
5. **No raw agent output.** Do not paste agent transcripts, session narration,
   or planning notes into issues, pull requests, commit messages, or
   documentation. Write for the reader.
6. **No unsolicited bulk submissions.** A large batch of generated proofs or
   documentation without prior discussion will be closed. Open an issue first
   if you want to do something at scale.
7. **Documentation stays timeless.** Documentation describes the system as it
   is. It does not narrate how it got that way, cite version numbers, or
   record what was validated when. That belongs in commit messages and
   release notes.

If you are configuring a coding agent to work in this repository, point it at
[AGENTS.md](AGENTS.md), which states these expectations in the form an agent
can follow.

## Licensing

Grace17 is licensed under the Apache License, Version 2.0. By contributing,
you agree that your contribution is licensed under the same terms. You retain
copyright in your work; the project does not require a copyright assignment
or a contributor license agreement. The `Signed-off-by` line on your commits
is your certification that you have the right to contribute the work.

## Conduct

Be kind, be specific, and assume good faith. Criticize mathematics and code,
not people. Newcomers to formal proof, and newcomers to set theory from other
proof assistants, should find this a welcoming place to ask basic questions.
