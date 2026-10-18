# Independent OCaml proof checkers

The OCaml implementation covers **all 30 G17M v4 opcodes** and **all admission
operations of the current G17C v3 format**. It independently constructs the ZF,
ZFC, or ZFG foundation, checks declaration proof obligations, and replays the
complete Cumulus library. Exact integers use Zarith (backed by GMP), alongside
the OCaml standard library.

Build with 64-bit OCaml 5.3, the version tested for this release:

```sh
opam install zarith
npm run build:ocaml
npm run conformance:ocaml
npm run test:ocaml
```

Set `OCAMLOPT=/path/to/ocamlopt` to select a compiler. Executables are written to
`build/ocaml/`. Zarith is located through `ocamlfind` when available, or under
the compiler library directory; set `ZARITH_DIR` for a custom installation.
Test drivers use Node to produce fixtures and Python to launch
and compare results; neither is used by the OCaml checker executables.

To check a standalone proof tape against its explicit logical environment:

```sh
build/ocaml/g17check build/Cumulus.g17m --environment build/Cumulus.g17env
```

To reconstruct Cumulus from the named foundation and checked Bootstrap:

```sh
npm run compile:cumulus
build/ocaml/g17c_check build/compiled/Cumulus.g17c \
  --foundation ZFG --dependency build/compiled/Bootstrap.g17c --json
```

`--foundation` also accepts a `.g17f` receipt. A receipt selects and checks
the result of foundation construction; it cannot supply axiom or theorem maps.
The G17C checker does not accept a `.g17env` in place of this construction.
Repeat `--dependency` for additional artifacts in the certified dependency
closure. Dependencies are replayed in the root module's declared order.

Exit status 0 means accepted. Status 1 means the input was rejected or checking
could not complete, including a resource limit. There is no "unsupported
computation" acceptance path and no fallback to another checker.

## Logical scope

`g17check` checks proofs relative to a supplied `.g17env`. Its digest binds the
proof to that environment; it does not justify the environment's axioms or
previously known theorems. Use `g17c_check` for the stronger end-to-end result:
foundation construction, declarations, theorem batches, dependencies, and the
final environment digest are all checked.

The implementation checks empty contexts at exported roots, bound-variable
scope, ordered branch contexts, substitutions, and eigenvariable conditions.
The computation rules use arbitrary-precision `Z.t` naturals. Addition, multiplication, factorial,
supported natural decision operations, and the natural predecessor, truncated
subtraction, remainder, and quotient use shortcuts only after matching
their defining equations. Other definitions use bounded equation evaluation.
Rational-class computation requires the proved quotient equality criterion,
natural arguments, positive denominators, and equal exact cross-products.
The exact list of computational definitions is checked as well as the result.

Ground evaluation (via the `compute` method) has a fuel budget of one
million steps per computation by default, set with `--fuel STEPS`, and multiplication has a
3,321,928-bit operand-size sum limit (approximately one million decimal digits).
Exhaustion rejects the certificate. These limits may reject a valid but
expensive proof, so acceptance is the meaningful result.

## Source map

| File | Responsibility |
|---|---|
| `support.ml` | JSON, UTF-16 canonical ordering, SHA-256 |
| `logic.ml`, `named.ml` | De Bruijn logic and named declaration syntax |
| `compute.ml` | Exact arithmetic and checked equation evaluation |
| `machine.ml` | G17M decoding, all inference rules, theorem boundaries |
| `environment.ml` | Signatures, closedness, deterministic environment state |
| `ast_proof.ml` | Declaration proof DAGs, including both induction rules |
| `admissions.ml` | Every supported conservative declaration operation |
| `foundation.ml` | Explicit ZF/ZFC/ZFG construction |
| `compiled.ml` | G17C event and dependency replay |

The test executables are separate from the two checker CLIs. The well-founded
admission unit test assumes two true lemmas in an isolated test environment;
those assumptions are not added to G17C or to Cumulus.

The checker is independently implemented and tested. It is not formally
verified, and it is not a metatheoretic proof of the calculus.

## Formatting

All OCaml sources use ocamlformat with the checked-in configuration. This
release uses ocamlformat 0.9, as a development tool only. Run
`npm run format:ocaml` to format and `npm run format:ocaml:check` to verify.
Set `OCAMLFORMAT_BIN` to select its executable. Change the formatter version
in its own formatting-only diff.

Canonical decimal strings remain the certificate encoding. They are validated
before conversion to `Z.t`; signed or noncanonical strings are rejected. Natural
subtraction truncates at zero. Loop counters are converted to machine integers
only after checking the fuel bound. There is no custom big-integer code.

Primitive natural recursion retains exact intermediate evaluations and the
largest completed prefix per fixed argument tuple within one evaluation. This
avoids repeated prefix construction when other recursive arguments change;
no result is reused across evaluator instances. `advance(120,3)=123` and the
public executable GCD certificate exercise this behavior. All values still
come from the admitted equations, with unchanged fuel and dependency checks.
