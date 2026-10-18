# Independent proof checkers

Grace17 ships three independent proof checkers. They share no code with the
TypeScript kernel and do not call it, and they share no code with each
other. Each implements the transition system of
[checker semantics](../docs/checker-semantics.md) from that page and the two
format pages, [kernel format](../docs/kernel-format.md) and
[compiled module format](../docs/compiled-module-format.md).

| Checker | Language | Dependencies |
| --- | --- | --- |
| `checkers/python` | Python 3 | none |
| `checkers/ocaml` | OCaml 5 | Zarith |
| `checkers/rust` | Rust 2021 | `num-bigint`, `sha2`, `serde_json` |

Each covers every G17M opcode and every G17C admission operation. For the
end-to-end module check, each builds the starting environment itself rather
than reading it from a file: the axioms of ZF, ZFC, or ZFG, the primitive
signature, and the prelude definitions are written into the checker, and the
digest of what it builds must match the digest the compiled module names.
Only the axioms are trusted. The prelude definitions (`subset`, `orderedPair`,
`functionOn`, etc.) are "built in" to the checkers in a weak sense: they are
processed automatically at checker boot, but they go through the same
conservative extension based principle of definition as everything else.
They are part of the boot because two axioms are stated in terms of them and
because every module names the digest that includes them.

Each checker has two entry points:

- `g17check CERTIFICATE --environment ENVIRONMENT` checks a G17M proof tape
  against an authenticated `.g17env` environment. The environment is logical
  input: the tape's proofs are replayed, and the environment's definitions and
  earlier theorems are taken as given.
- `g17c_check CERTIFICATE --foundation ZFG [--dependency FILE]...` is the
  strict end-to-end check. It constructs the named foundation itself, replays
  every dependency artifact and every admission event of the module, checks
  every embedded theorem batch, and requires the final environment digest.
  A trusted `.g17env` snapshot is never accepted as a foundation.

Exit status 0 means accepted; status 1 means rejected or unable to complete,
including a resource limit. There is no partial acceptance and no fallback
to another checker. With `--json`, each prints one JSON object with `ok`,
`checker`, and either the counts it checked or a `message`.

## Running them

```sh
npm run conformance:python   # the corpus with the Python checker
npm run test:ocaml           # build, corpus, and declaration obligations
npm run test:rust            # build, corpus, and an example tape
npm run compile:cumulus      # export the complete library as G17C
npm run check:g17c:python    # replay the library: Python
npm run check:g17c:rust      # replay the library: Rust
```

The [conformance corpus](../docs/conformance.md) under `conformance/` holds
one accepted and one rejected tape per opcode plus focused attacks; every
checker must agree on all of them. Full-library replay is the stronger test:
`build/compiled/Cumulus.g17c` with its `Grace.Bootstrap` dependency is
replayed from the bare ZFG axioms to the same environment digest the kernel
reports.

## Current independent proof checkers

**Python** (`g17check.py`, `g17c_check.py`) is the readable reference: no
dependencies beyond the standard library, written to be compared line by
line with the specification. It is the slowest of the three, so its replay
of the complete library is a local and release check
(`npm run check:g17c:python`); continuous integration replays the library
with the Rust checker on every push.

**OCaml** (`machine.ml`, `admissions.ml`, `compute.ml`, and friends) is the
first compiled implementation.

**Rust** (`src/machine.rs`, `src/admissions.rs`, `src/compute.rs`, and
friends) is the fastest. It is also the natural starting point for a checker
that runs where neither Python nor OCaml is available.

Resource limits are part of each checker's specification. Ground evaluation
(via the `compute` method) has a fuel budget of one million steps per
computation by default; `--fuel STEPS` sets another budget on every checker
and both entry points, and exhausting it rejects. These limits may reject a
valid but expensive certificate, so acceptance is the meaningful result and a
rejection on a limit is reported as such.

## Reporting a problem

A certificate that one checker accepts and another rejects, or one that any
checker accepts although its claim is false, is a soundness report and takes
priority over everything else. See [soundness](../docs/soundness.md) for the
trusted boundary and [contributing](../CONTRIBUTING.md) for how to report.
