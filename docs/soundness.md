# Soundness and the trusted boundary

This document records what Grace17 trusts and how that trust is checked. It
is an engineering account. There is no machine-checked metatheorem about the
calculus yet; a proved connection between an executable checker and the
semantics is a research goal, and the path toward it is at the end.

## What is trusted

Four layers are inside the trusted boundary:

1. the named-AST natural-deduction checker and the environment-event
   validators that admit definitions, datatypes, Separation and Replacement
   instances, and recursion;
2. the numeric de Bruijn proof-machine checker for the G17M tape format;
3. the independent checkers in Python, OCaml, and Rust, which replay the same bytes;
4. the ground evaluator used by the primitive `compute` rule, including its
   exact arithmetic-schema recognition and host big-integer arithmetic.

Everything else is an untrusted proof producer: parsing, elaboration, tactics,
proof search, soft-type inference, proof maps, library search, and the
Workbench. Their output must pass a checker above before a theorem is
admitted.

The [kernel format](kernel-format.md) is the normative, language-independent
specification of the proof language. A conforming checker computes each
instruction's conclusion itself, validates contexts and eigenvariable side
conditions, rejects forward theorem references, and authenticates both the
proof tape and its environment.

## Independent checkers

Four implementations check the same certificates:

| Checker | Language | Scope |
| --- | --- | --- |
| Reference kernel | TypeScript | Named AST rules, environment events, numeric G17M machine, G17C compiled modules |
| `checkers/python` | Python, no dependencies | Every G17M opcode; full G17C replay that reconstructs the ZF, ZFC, or ZFG foundation itself |
| `checkers/ocaml` | OCaml with Zarith | The same |
| `checkers/rust` | Rust with `num-bigint`, `sha2`, and `serde_json` | The same |

The independent checkers share no code with the TypeScript kernel and do
not call it. All of them implement the transition system of
[checker semantics](checker-semantics.md). Each independent checker's `g17c_check` is the strongest end-to-end
result: it constructs the foundation, checks every declaration event, replays
every theorem, and authenticates the final environment digest without reading
an authoritative environment file. See [the checkers](../checkers/README.md).

The [conformance corpus](conformance.md) is the executable compatibility
contract. It contains one positive and one false-claim negative vector for
every opcode, plus focused attacks on binder freshness, eigenvariable
conditions, and exact computation dependencies. All three checkers must
accept and reject the same vectors.

## Environment events

A proof-tape check against an exported environment and a complete
reconstruction of that environment are different validation tasks. A
`g17check` run treats the authenticated environment as logical input: it
verifies proof replay and takes the definition, datatype, Separation,
Replacement, and recursion events on trust. The G17C format and each
checker's `g17c_check` close that gap by replaying the events themselves from
the named foundation. See [foundation bootstrap](foundation-bootstrap.md) and
[compiled module format](compiled-module-format.md).

## Path toward proved checkers

1. Expand the conformance corpus to one focused negative vector for every
   distinct rule side condition.
2. Keep adding small checkers in languages with different failure modes.
3. Give the G17M calculus a mathematical small-step specification independent
   of any file parser.
4. Prove soundness of that calculus with respect to first-order semantics.
5. Verify at least one decoder and replay loop against the specification.
6. Reduce environment-building events to proof-producing conservative
   extensions wherever practical.

The target is a small specified proof language, several independent replay
checkers, and a formal theorem connecting at least one executable checker to
the semantics.

## Reporting a soundness problem

If you believe you have a certificate that a checker accepts but should not,
or a surface proof of a false statement, please open an issue with the
smallest reproduction you can manage. Soundness reports take priority over
everything else. See [CONTRIBUTING.md](../CONTRIBUTING.md).
