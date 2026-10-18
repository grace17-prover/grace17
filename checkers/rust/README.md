# Independent Rust proof checkers

The Rust implementation covers **all 30 G17M v4 opcodes** and **all admission
operations of the current G17C v3 format**. It independently constructs the
ZF, ZFC, or ZFG foundation, checks declaration proof obligations, and replays
the complete Cumulus library. It implements the transition system of
[checker semantics](../../docs/checker-semantics.md) and shares no code with
the TypeScript kernel or with the Python and OCaml checkers.

Build with a stable Rust toolchain (1.80 or later is tested):

```sh
npm run build:rust          # cargo build --release, unit tests, copies to build/rust/
npm run conformance:rust    # the 66-vector corpus plus three mutations
npm run check:rust          # an example tape against its environment
```

The crate depends on `num-bigint` for exact naturals, `sha2` for SHA-256,
and `serde_json` for the JSON environment and module formats. Executables
are written to `build/rust/`.

To check a standalone proof tape against its explicit logical environment:

```sh
build/rust/g17check build/Cumulus.g17m --environment build/Cumulus.g17env
```

To reconstruct Cumulus from the named foundation and checked Bootstrap:

```sh
npm run compile:cumulus
build/rust/g17c_check build/compiled/Cumulus.g17c \
  --foundation ZFG --dependency build/compiled/Bootstrap.g17c --json
```

`--foundation` also accepts a `.g17f` receipt, which selects and checks the
result of foundation construction; a `.g17env` snapshot is never accepted in
its place. Repeat `--dependency` for every artifact in the dependency
closure; they are replayed in the root module's declared order.

Exit status 0 means accepted. Status 1 means the input was rejected or
checking could not complete, including a resource limit. There is no
"unsupported" acceptance path and no fallback to another checker. With
`--json` the checker prints one JSON object: `{"ok":true,...}` with the
counts it checked, or `{"ok":false,"checker":"grace17-rust","message":...}`.

## Logical scope

`g17check` checks proofs relative to a supplied `.g17env`; its digest binds
the proof to that environment, and the environment's axioms and earlier
theorems are logical input. `g17c_check` is the stronger end-to-end result:
foundation construction, every declaration event, every theorem batch,
every dependency receipt, and the final environment digest are all checked.

The implementation checks empty contexts at exported roots, bound-variable
scope, ordered branch contexts, substitutions, eigenvariable conditions, and
the freshness conditions of induction. Computation uses arbitrary-precision
naturals; addition, multiplication, factorial, the natural decision
procedures, and the natural predecessor, truncated subtraction, remainder,
and quotient use big-integer shortcuts only after their defining equations
have matched exactly, and every other definition goes through the bounded
equation interpreter. The exact list of unfolded definitions is checked as
well as the result.

Ground evaluation (via the `compute` method) has a fuel budget of one
million steps per computation by default, set with `--fuel STEPS`, and
definitional normalization of ordinal interfaces a ten-thousand-step limit.
Exhaustion rejects. The checker runs on a thread with a 512 MB stack so that a deep
proof is a rejection on a limit rather than a crash.

## Source map

| File | Responsibility |
| --- | --- |
| `src/support.rs` | failure type, canonical LEB128, canonical JSON, SHA-256 |
| `src/ast.rs` | named terms, formulas, patterns, binding operations |
| `src/machine.rs` | G17M decoding, arena interning, the thirty rules, boundaries |
| `src/compute.rs` | the equation interpreter, admitted shortcuts, rational classes |
| `src/environment.rs` | the environment, its snapshot, and its digest |
| `src/admissions.rs` | every G17C admission event, proof DAGs, module replay |
| `src/foundation.rs` | the normative ZF, ZFC, and ZFG construction |
| `src/bin/g17check.rs`, `src/bin/g17c_check.rs` | the command lines |

`check_conformance.py` is a test harness; the checker never invokes Python.
