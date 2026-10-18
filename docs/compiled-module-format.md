# Grace17 checked compiled modules (G17C)

Status: versions 1, 2, and 3, executable reference implementation in
`src/compiled-module.ts`. Normative foundation construction is specified in
`foundation-bootstrap.md`.

## 1. Trust boundary

A G17C file is a certificate for extending an existing kernel environment. It
is not a serialized kernel, and a correct digest grants no declarations. The
digest identifies content; it carries no logical authority.

A checker accepts a G17C file only by:

1. checking its canonical encoding and content digest;
2. checking that the current kernel digest is exactly `baseEnvironment`;
3. replaying every event, in order, through the corresponding checked kernel
   operation;
4. checking that the reconstructed kernel digest is exactly
   `resultEnvironment`.

The input kernel is not mutated. Replay occurs in a fresh monotone fork, which
is returned only after every event and the final digest have passed.

Parsing `.g17` source, resolving names, elaborating soft types, running tactics,
and searching for proofs are outside G17C replay. A surface-language index may
accompany a compiled module for editor services, but it is untrusted and cannot
admit a proposition.

## 2. Canonical envelope

A compiled module is canonical UTF-8 JSON, format version 3:

```json
{
  "format": "grace17.compiled-module",
  "version": 3,
  "module": "Grace.Cumulus.NumberTheory.Prime",
  "source": "optional source SHA-256",
  "foundation": { "profile": "ZFG", "environment": "foundation digest" },
  "dependencies": [
    { "module": "Grace.Core", "digest": "content digest" }
  ],
  "baseEnvironment": "exact foundation-plus-dependencies digest",
  "events": [],
  "resultEnvironment": "exact strict-replay result digest",
  "digest": "artifact content digest"
}
```

Canonical JSON is the `canonical` encoding specified for G17M environments:
arrays retain order, object keys are sorted by JavaScript UTF-16 code-unit
order, and no insignificant whitespace is present. `digest` is SHA-256 of the
canonical envelope with the `digest` field omitted.

`foundation` names the profile and the digest the checker-constructed
foundation must reach. `dependencies` is the entire dependency closure in
replay order, not only the direct imports; the redundancy keeps an
independent checker small, since it needs no namespace resolver, package
solver, or graph canonicalizer. Dependencies are descriptive
content-addresses and do not replace the base environment check: their
admitted contents are already committed to by `baseEnvironment`. The event
order is semantically significant.

## 3. Events

An event is either an admission, `{ "kind": "admission", "event": { "operation": string, "payload": object } }`,
or a theorem batch, `{ "kind": "theoremBatch", "statements": [...], "machine": {...} }`.
The admission operations and payloads are:

| Operation | Payload |
|---|---|
| `declareFunction` | `{name, arity}` |
| `declarePredicate` | `{name, arity}` |
| `defineFunction` | `{name, parameters, body}` |
| `definePredicate` | `{name, parameters, body}` |
| `declareDatatype` | `{spec}` |
| `defineStructuralFunction` | `{options}` |
| `defineWellFoundedFunction` | `{options}` including all termination proofs |
| `defineSubset` | `{name, parameters, element, bound, condition}` |
| `reifyUnaryOperation` | `{options}` including the closure proof |
| `defineReplacement` | `{options}` including the functionality proof |
| `defineUniqueFunction` | `{options}` including the unique-existence proof |
| `defineWellFoundedSetFunction` | `{options}` including well-foundedness |
| `defineMembershipRecursiveFunction` | `{options}` |
| `defineTransfiniteFunction` | `{options}` including its guarded interfaces |

The fields in each `options` object are the fields of the same-named public
operation in `src/kernel.ts`. A checker must call that operation; it must not
copy the operation's resulting map entries from the file. In particular,
datatype positivity and coverage, recursive descent, Separation, Replacement
functionality, unique existence, well-foundedness, the canonical ordinal
interface, and guarded transfinite clauses are all checked again.

An implementation must reject unknown operations and unknown event kinds. It may validate structural
fields before replay, but the kernel operation remains authoritative.

`addAxiom` is not a G17C library event. The selected ZF/ZFC/ZFG foundation and
its axioms must already be present in the base environment. Compiling an
admission interval that contains a new axiom fails, so a library artifact
cannot add foundational strength.


A theorem batch replaces every maximal consecutive sequence of admitted
theorems with one event. It contains the named statements and one shared
G17M v4 symbol, term, formula, context, and instruction arena.
The batch is checked in the live environment produced by all preceding G17C
events. Its standalone G17M `environment` field is not used to re-hash the
entire growing environment: the containing G17C base digest and event order
already bind that state, while G17M signature and dependency checks consult the
live kernel directly. Standalone G17M verification still requires exact
environment digest equality.

Every statement must match its corresponding checked machine boundary. A
reference to another theorem in the same batch is valid only when that
theorem's boundary precedes the referring instruction. No statement is
installed until the complete program and all boundaries pass, so batch
admission is atomic.

## 4. Proof values

Every value whose root is a primitive Grace17 proof is replaced recursively by:

```json
{ "$grace17ProofDag": { "version": 1, "nodes": [], "root": 0, "digest": "..." } }
```

This is the authenticated proof DAG specified in `src/dag.ts`. References must
point strictly backward. On replay the DAG is authenticated and decoded, then
the receiving admission operation checks the proof in the environment produced
by all preceding events. Thus a theorem cannot cite itself or a later theorem,
and a schema certificate cannot use declarations that had not yet been
admitted.

Changing a proof and recomputing every content digest does not make it valid.
The replayed kernel judgment must still derive the required formula.

## 5. Determinism and module composition

Compilation begins at a `KernelAdmissionCheckpoint`, which records the base
environment digest and event offset. Successful public kernel admissions are
then emitted in their original order. Compilation records the final kernel
digest. Given the same base, source, and compiler version, the resulting event
semantics and reconstructed kernel environment are deterministic.

For separate compilation, replay imports in the language-defined import order.
The resulting digest after the imports is the dependent module's
`baseEnvironment`. A stale, missing, reordered, or differently configured
dependency therefore fails before the first local event.

## 6. Separate modules and receipts

A module records its foundation and its complete ordered dependency closure,
as in the envelope above.

`dependencies` is the entire dependency closure in replay order, not only the
direct imports. The redundancy keeps an independent checker small: it needs
no namespace resolver, package solver, or graph canonicalizer.

A strict checker implements one streaming procedure:

1. construct the named foundation through the normative bootstrap and check its digest;
2. replay each dependency artifact in the listed order, checking its receipt;
3. require the resulting digest to equal `baseEnvironment`;
4. replay local events through the kernel;
5. require `resultEnvironment`, then retain `(module, digest)` as a receipt.

The TypeScript reference function is `replaySeparateKernelModuleExact`. Its
extra state is only a map from module names to 32-byte content digests. It does
not need source syntax, surface types, tactics, editor data, or a serialized
kernel snapshot.

`checkers/python/g17c_check.py` is an independent, dependency-free
implementation of this strict path, and `checkers/ocaml` and `checkers/rust`
are two more. Each constructs ZFG itself and reconstructs the complete
current Cumulus library through every admission operation of the table
above. An admission operation a checker does not know is rejected.

The accepted foundation argument is a normative profile name or tiny `.g17f`
receipt containing only `{format, version, profile, environment}`. A strict
G17C check rejects `.g17env` snapshots. Both reference implementations produce
the same environment digest independently for ZF, ZFC, and ZFG.

The distributed Cumulus artifact has `Grace.Bootstrap` as its first exact
dependency. That small G17C module contains one dense G17M batch proving the
public compatibility aliases from canonical axioms. A checker must replay its
certificate and retain its content receipt before Cumulus can pass its exact
dependency-prefix check; a claimed post-bootstrap environment is never loaded.

Embedded theorem batches do not cause an intermediate whole-environment hash.
The authenticated G17C event order and final environment digest already bind
the state, while the G17M checker validates every live signature, dependency,
instruction, and theorem boundary.

An editor may already contain unrelated, monotonically admitted modules.
`replaySeparateKernelModule` accepts that case only when the foundation and
every dependency receipt match; it still replays and checks every local
event. Receipts are not part of the logical environment digest and proof
checking never consults them; they record cache provenance. A fresh
independent checker should use strict replay.

### Surface-index sidecar

`grace17.surface-index` version 3 is canonical JSON containing module scopes,
declared namespace provenance, exported opens, soft classes, signatures, notation, tactic macros, and datatype
presentation metadata. It is bound to both a version-3 module digest and the
exact reconstructed kernel environment. It may be installed only after that
module receipt and environment match.

The sidecar is untrusted. It can influence parsing, name resolution, hover
information, and elaboration, but every term, formula, definition, and proof it
helps produce must pass the kernel checks. Independent proof checkers ignore
it. The optional nonnegative integer `requirementCount` on theorem signatures
records the number of source `requires` clauses, excluding generated binder
guards. It lets `with *` stop at the declared conclusion; it neither certifies
nor discharges a premise. Signatures without this field keep the
implication-chain application behavior.

### Closure artifacts

A module store keeps one version 3 artifact per library module, compiled
against the module's own import closure rather than against a global prefix.
`dependencies` still lists the whole closure, in a topological order, but
`baseEnvironment` is the digest of the foundation plus exactly that closure as
a set. Environment digests are order-free, so a strict checker reconstructs the
base by replaying the listed artifacts in the listed order, checking each
receipt and every event, then checks `baseEnvironment`, replays the module,
and checks `resultEnvironment`. The reference functions are
`compileSeparateKernelModuleOverClosure` and, unchanged,
`replaySeparateKernelModuleExact`. The chain form of section 7 remains the
format of the distributed whole-library artifact.

`src/module-store.ts` is the build driver. `g17 build --module-root lib
--artifacts build/modules lib/Grace/Cumulus.g17` writes
`build/modules/<Module.Name>.g17a`, a JSON record holding the compiled module,
the surface delta the module adds for the elaborator (notation, signatures,
instances, tactics, and carrier annotations), the module's report data, and
the digests of its source and of each closure artifact. An artifact is current
when its source digest and every closure digest match, so an edit rebuilds the
edited module and its dependents only. `g17 check --artifacts build/modules`
loads a file's imports from the store, building what is missing or stale, and
elaborates only files outside the module roots from source. The store is a
cache: every load replays each artifact through the checked kernel and binds
the surface delta to the module's receipt, and a corrupted or inconsistent
artifact is rejected.

An artifact file is canonical JSON with its digest first: the text after the
opening `{"digest":"…",` is exactly the canonical serialization of the rest
of the record, and the digest is the SHA-256 of that serialization. A reader
therefore verifies the bytes it was handed against the digest its dependents
recorded without re-serializing anything, and the compiled module inside is
then accepted on that verification; its proofs are still replayed by the
kernel. After replay the kernel keeps the statements and, for the verified
machine programs, only a loader: an axiom audit reloads a program from the
same artifact, which must still carry the digest that was loaded.

The store also holds a foundation artifact, `foundation.<profile>.g17f`: the
bootstrap prelude compiled over the bare axioms as replayable events, with
its surface delta and the digest of the prelude's sources. A store kernel
replays it instead of elaborating the prelude, and the replay must reach the
foundation digest that every compiled module names; when the sources have
changed, the prelude is elaborated and the build writes a new artifact.

`bin/g17.ts` is a launcher: the command line lives in `src/cli.ts`, and a run
loads a plain JavaScript copy of the sources under `build/cli`, rebuilt by
`scripts/build-cli.ts` whenever a source file is newer than the copy's stamp.

## 7. Dense binary encoding

A production binary encoding must keep the replay algorithm above and replace
the representation with:

- one shared symbol, term, and formula arena for the module;
- one dense proof-instruction arena with theorem/schema-certificate roots;
- compact integer event opcodes and arena references;
- independently hashed surface-index and tactic-provenance sections;
- optional block hashes so unchanged dependency prefixes can be cached.

Cold loading then approaches G17M machine-replay speed, with no
kernel-snapshot deserializer and no second admission semantics.

## Independent replay

The Python, OCaml, and Rust implementations each support every admission
operation in the current v3 format, reconstruct ZF/ZFC/ZFG independently, and
check declaration proof DAGs and G17M batches. Each reproduces the complete
Cumulus environment without reading an authoritative `.g17env`. See
`checkers/README.md`.
