# Grace17 kernel and G17M format

This document tells an implementer what a Grace17 proof checker must do. It
uses direct prose and integer layouts. It does not describe parsing, tactics,
type inference, or proof search, because none of those belong in a checker.

The current portable proof format is G17M version 4. Complete, independent
implementations are in `checkers/python/g17check.py`, `checkers/ocaml`, and
`checkers/rust`, each with a strict G17C v3 library checker beside it
(`g17c_check`). See `checkers/README.md`.

For loading compiled libraries, use the checker-constructed foundation in
`foundation-bootstrap.md` and the checked G17C event format specified in
`compiled-module-format.md`. A `.g17env` snapshot is an explicit logical input
only to a standalone G17M proof check. The full G17C checker rejects it; that
checker constructs the foundation and replays library declarations itself.

The rules this format encodes are stated as a transition system in
[checker semantics](checker-semantics.md); this page fixes the bytes.

## 1. What the checker receives

The standalone G17M checker receives two files:

1. a `.g17env` environment;
2. a `.g17m` proof tape.

The environment gives the function and predicate signatures, axioms,
previously known theorems, definitions, datatypes, and recursive equations.
The proof tape gives formulas and a forward list of primitive inferences.

The proof tape contains the SHA-256 digest of its environment. Reject the tape
if this digest differs from the checked environment digest.

The checker must not run tactics. It must not trust a claimed conclusion. For
each instruction it computes the only formula that the instruction can derive,
then compares that formula with the claimed formula ID.

The end-to-end G17C checker instead receives a named normative foundation (or
its `.g17f` receipt) and an ordered closure of G17C artifacts. It constructs
the foundation, replays every checked admission, and uses G17M for theorem
batches. No `.g17env` is trusted on this path.

## 2. Logical language

Grace17 is one-sorted first-order logic with equality. Every object is a set.
Names such as `Nat` are predicates; the kernel has no types.

### Terms

| Integer node | Meaning |
|---|---|
| `[0, s]` | free variable whose name is symbol `s` |
| `[1, i]` | bound variable with de Bruijn index `i`; `0` is the nearest binder |
| `[2, f, a0, ..., an]` | application of function symbol `f` to term nodes `a0 ... an` |
| `[3, s]` | natural literal; symbol `s` must be `0` or a decimal with no leading zero |

Natural node `[3,"n"]` is definitionally the same term as `n` applications of
`succ` to `zero`. A checker should store it as an arbitrary-precision
nonnegative integer. When interning terms, fold `zero()` to natural `0` and
`succ(natural n)` to natural `n+1`.

### Formulas

| Integer node | Meaning |
|---|---|
| `[0]` | false |
| `[1, a, b]` | `a = b` |
| `[2, p, a0, ..., an]` | predicate `p(a0,...,an)` |
| `[3, A, B]` | `A -> B` |
| `[4, A]` | `forall x, A`; occurrences of `x` are de Bruijn index `0` |
| `[5, A, B]` | `A and B` |
| `[6, A, B]` | `A or B` |
| `[7, A, B]` | `A iff B` |
| `[8, A]` | `exists x, A` |

Term application children must refer to earlier term nodes. Formula children
of binary connectives and quantifiers must refer to earlier formula nodes.
Equality and predicate arguments may refer to any term node because the term
arena is read first.

Alpha-equivalent formulas have identical arena form because binders use de
Bruijn indices.

## 3. Portable environment

A `.g17env` file is UTF-8 JSON:

```json
{
  "format": "grace17.environment",
  "version": 1,
  "digest": "64 lowercase hexadecimal characters",
  "kernel": { "...": "canonical kernel snapshot" }
}
```

Compute the digest as SHA-256 of the UTF-8 bytes of `canonical(kernel)`.
Canonical encoding is small:

- null, booleans, integers, and strings use their JSON spelling;
- arrays retain their order and contain no spaces;
- object keys are sorted in JavaScript UTF-16 code-unit order;
- every sorted kernel-environment name array uses that same UTF-16 code-unit
  order, never locale-sensitive collation;
- objects contain no spaces.

The `kernel` object has these fields:

| Field | Representation |
|---|---|
| `capabilities` | foundation capability object |
| `functions` | sorted `[name, arity]` pairs |
| `predicates` | sorted `[name, arity]` pairs |
| `axioms` | sorted `[name, formula-AST]` pairs |
| `theorems` | sorted `[name, formula-AST]` pairs |
| `definitions` | sorted pairs containing kind, parameters, and named formula properties |
| `datatypes` | sorted `[name, datatype-record]` pairs; a record contains its predicate, Set parameters, constructors, recursive and parameter-field indices, and `setTheoreticEncoding` flag |
| `recursiveFunctions` | sorted `[name, recursive-record]` pairs |
| `functionBodies` | sorted `[name, {parameters, body}]` pairs |

Formula AST tags are `bottom`, `eq`, `pred`, `imp`, `forall`, `and`, `or`,
`iff`, and `exists`. Term AST tags are `var`, `app`, and `nat`. Pattern tags
are `bind` and `ctor`. Their fields are visible in the JSON.

Before checking a tape, verify the environment digest. Check every application
and predicate node against the environment arity tables.

### Building an environment

The Python checker treats the authenticated environment as its logical input,
just as a Metamath checker treats the database's constants and axioms as input.
An implementation that also builds environments must enforce these event
rules:

- A function or predicate declaration has a fresh nonempty name and a
  nonnegative finite arity.
- An axiom has a fresh name and a closed, well-signed formula.
- A theorem is inserted only after its proof has checked in the environment
  that existed before insertion. This prevents self-reference.
- An explicit function definition has a fresh function name, distinct
  parameters, no self-reference, and no free body variables other than its
  parameters. Its property is the universal closure of
  `f(parameters) = body`.
- An explicit predicate definition obeys the same conditions and records the
  universal closure of `P(parameters) iff body`.
- A Separation event checks its bounding set and condition, permits only the
  declared parameters and element variable free, and records
  `x in S(parameters) iff x in bound and condition`.
- A Replacement event checks a proof that its relation is total and
  single-valued on the bounding set before recording the image membership law.
- A unique-description event checks a proof of existence and uniqueness before
  installing its fresh function and characterization.
- A set-well-founded recursion event checks the well-foundedness theorem for
  its formula-defined relation. Its history is a restricted set graph and
  its step may depend only on the declared parameters, current point, and
  history. It installs no executable body. The conservative event exposes the
  Replacement-built predecessor/value history through a membership
  characterization and records a direct, domain-guarded defining equation in
  addition to the unique solution-graph properties.
- A transfinite-recursion event requires Separation, Replacement, and
  Foundation. It checks that the successor index definitionally normalizes to
  `alpha union {alpha}` and that any user-facing `Ordinal` and `Limit`
  conditions definitionally unfold to the canonical von Neumann formulas. The
  zero and limit clauses contain no recursive call; every successor-clause call
  is at the immediate predecessor. The event installs a nonexecuting
  function, a Replacement-backed history function, and zero, successor, limit,
  history-membership, and outside-domain properties. An independent
  environment builder must repeat these guards before authenticating a tape.
- A datatype declaration uses fresh constructor names, distinct Set parameters,
  and valid disjoint recursive-field and parameter-field indices. Its constructor
  properties require the parameterized datatype predicate on every recursive
  field, membership in the selected carrier for every parameter field, and
  conclude the predicate for the constructed value. It also records exhaustive
  cases, constructor injectivity, and pairwise disjointness. A surface
  algebraic datatype also sets `setTheoreticEncoding` and records each
  constructor's equality with a stable tagged Kuratowski encoding. The built-in
  von Neumann naturals do not use this generic encoding.
- A structural recursive definition has exactly one equation per constructor,
  matches only its designated decreasing parameter, uses linear patterns, and
  makes every recursive call on a variable from a recursive constructor field.
- A well-founded recursive definition has exhaustive constructor coverage plus
  checked proofs of well-foundedness, measure-domain membership, and strict
  decrease for every recursive call.

ZF, ZFC, and ZFG differ only in their declared foundational axioms and choice
capabilities. The exact names and formulas are visible in the environment; no
foundation axiom is hidden in G17M replay.

## 4. G17M binary layout

All counts, indices, and instruction words are unsigned canonical LEB128.
Reject a value longer than five bytes, greater than `2^32-1`, or encoded with a
redundant final zero group.

The file is, in order:

| Field | Encoding |
|---|---|
| magic | four bytes `47 31 37 4d`, ASCII `G17M` |
| version | one byte, currently `4` |
| flags | one byte: `0` for an unlinked tape, `1` for a linked theorem module |
| environment | 32 raw SHA-256 bytes |
| symbols | count, then each UTF-8 string as byte-count and bytes |
| terms | vector of integer vectors |
| formulas | vector of integer vectors |
| contexts | vector of integer vectors |
| code | vector of integer vectors |
| root | instruction index |
| theorem boundaries | count, then repeated `(name-symbol, root-instruction)` pairs |
| file digest | 32 raw SHA-256 bytes over every preceding byte |

A vector of vectors is an outer count followed by, for each vector, its word
count and words. UTF-8 must decode strictly and re-encode to the same bytes.

Flags must be `1` when the theorem-boundary list is nonempty and `0` otherwise. Symbols,
term nodes, formula nodes, and contexts are canonical intern tables: reject an
empty or duplicate symbol and reject duplicate nodes within each arena.

Limits in version 4 are 10,000,000 entries per arena and 1,000,000 words per
vector or bytes per string. An implementation may impose smaller documented
resource limits. Reaching a limit must reject, never accept.

## 5. Contexts and instructions

A context is an ordered vector of formula IDs. Order matters. Extending context
`G` with formula `A` produces the vector `G` followed by `A`.

Every instruction is:

```text
[opcode, claimed-formula, context, premise-count, premise-ids..., rule-data...]
```

Every premise ID must be smaller than the current instruction ID. Unless a
rule below says that a branch has an extended context, every premise must have
the instruction's context.

The following table is normative. `result(i)` means the formula derived at
instruction `i`. `Eq(a,b)`, `Imp(A,B)`, and similar names mean interned arena
nodes.

| Op | Rule | Premises | Data | Required result and checks |
|---:|---|---:|---|---|
| 0 | assumption | 0 | `A` | `A`; context must contain `A` |
| 1 | axiom | 0 | `name` | the environment axiom named `name` |
| 2 | theorem | 0 | `name` | an external theorem, or an earlier checked boundary named `name` |
| 3 | definition | 0 | `name, property` | that named definition property |
| 4 | reflexivity | 0 | `t` | `Eq(t,t)` |
| 5 | symmetry | 1 | none | from `Eq(a,b)`, derive `Eq(b,a)` |
| 6 | transitivity | 2 | none | from `Eq(a,b)` and `Eq(b,c)`, derive `Eq(a,c)` |
| 7 | congruence | function arity | `f` | from each `Eq(ai,bi)`, derive `Eq(f(ai...),f(bi...))` |
| 8 | implication introduction | 1 | `A` | premise context is `G,A`; from `B`, derive `Imp(A,B)` in `G` |
| 9 | implication elimination | 2 | none | from `Imp(A,B)` and `A`, derive `B` |
| 10 | universal introduction | 1 | free-symbol `x` | abstract free `x` in premise; `x` must not be free in context |
| 11 | universal elimination | 1 | term `t` | instantiate the outer binder with `t` |
| 12 | datatype induction | case count | dynamic | described below |
| 13 | equality elimination | 2 | `x, motive, reverse` | substitute the selected sides of an equality for free `x` in `motive`; `reverse` is 0 or 1 |
| 14 | conjunction introduction | 2 | none | from `A` and `B`, derive `And(A,B)` |
| 15 | left conjunction elimination | 1 | none | from `And(A,B)`, derive `A` |
| 16 | right conjunction elimination | 1 | none | from `And(A,B)`, derive `B` |
| 17 | left disjunction introduction | 1 | `B` | from `A`, derive `Or(A,B)` |
| 18 | right disjunction introduction | 1 | `A` | from `B`, derive `Or(A,B)` |
| 19 | disjunction elimination | 3 | none | first premise is `Or(A,B)` in `G`; branches use `G,A` and `G,B` and derive the same `C`; result is `C` |
| 20 | equivalence introduction | 2 | none | from `Imp(A,B)` and `Imp(B,A)`, derive `Iff(A,B)` |
| 21 | forward equivalence elimination | 1 | none | from `Iff(A,B)`, derive `Imp(A,B)` |
| 22 | backward equivalence elimination | 1 | none | from `Iff(A,B)`, derive `Imp(B,A)` |
| 23 | existential introduction | 1 | `x, open-body, witness` | abstract free `x` in `open-body` for the conclusion; premise is open-body with witness substituted for `x` |
| 24 | existential elimination | 2 | fresh-symbol `w` | first premise is `Exists(A)` in `G`; second uses `G,A[w]`; `w` is fresh and may not occur in the result |
| 25 | false elimination | 1 | `C` | from false, derive `C` |
| 26 | double-negation elimination | 1 | `A` | from `Imp(Imp(A,false),false)`, derive `A` |
| 27 | well-founded induction | 2 | `relation, domain, x, y, motive` | described below |
| 28 | ground computation | 0 | `count, definition-names...` | described in section 7 |

Reject trailing or missing rule-data words. Opcode 12 and opcode 28 are the
only variable-length data layouts.

### Datatype induction data

Opcode 12 data is:

```text fragment
datatype-name, induction-variable, motive, parameter-count, parameter-terms...,
  case-count,
  constructor-name, field-count, field-symbols...,
  ... one constructor record per case
```

The parameter count must match the datatype declaration. Parameter terms are
well-formed and may not contain the induction variable. There must be exactly
one case for every constructor. Field symbols are distinct, differ from the
induction variable, and are fresh for the parent context, every parameter
term, and the open motive. For each recursive field, extend
the case context first with the datatype predicate applied to the parameters
and that field, and then with the motive instantiated at that field. For each
parameter field, extend the context with membership in its selected carrier.
The case must prove the motive at the constructor application. The result is:

```text
forall x, DatatypePredicate(parameters..., x) -> motive(x)
```

### Well-founded induction

Opcode 27 uses two premises in the same context. The first must prove
`wellFoundedOn(relation,domain)`. The second must prove:

```text
forall x,
  x in domain ->
  (forall y, (y in domain and relates(relation,y,x)) -> motive(y)) ->
  motive(x)
```

Symbols `x` and `y` must be distinct and absent from the context; `y` must not
be free in the open motive. The relation and domain may contain outer
parameters, but neither may contain `x` or `y`. The result is:

```text
forall x, x in domain -> motive(x)
```

## 6. Binding operations

Implement these operations directly on arena nodes:

- **abstract**: replace a chosen free-variable symbol by the current de Bruijn
  depth; increase depth when entering `forall` or `exists`;
- **instantiate**: replace de Bruijn index equal to the current depth by the
  replacement term shifted by that depth; decrement larger indices;
- **free substitution**: replace only free-variable nodes having the chosen
  symbol; bound nodes are untouched;
- **free-variable test**: inspect only free-variable nodes and recurse through
  applications and formulas.

All constructors created by these operations go through the same interner,
including natural folding for `zero` and `succ`.

## 7. Ground computation

Opcode 28 proves equality of two closed terms. Its data begins with a count and
then exactly that many definition-name symbols. Names must be unique and
lexicographically sorted.

Use this value domain:

```text
Value = Natural(arbitrary-precision nonnegative integer)
      | Application(function-name, Value...)
```

Normalize arguments before their application. Interpret `zero()` as natural
0 and `succ(n)` as `n+1` when `n` is natural. Unfold an explicit or recursive
definition only when its name occurs in the instruction's allow-list.
Otherwise retain an `Application` value.

For an explicit definition, bind parameters to normalized arguments and
evaluate its body. For a recursive definition, match its admitted constructor
patterns. `zero` matches 0; `succ(p)` matches a positive natural and binds
against one less; other constructors match `Application` values.

Record every definition unfolded. After normalizing both sides:

1. their values must be structurally equal;
2. the sorted set of definitions used must equal the supplied list.

The second condition keeps a certificate from quietly gaining access to more
executable definitions than it names.

A checker may recognize these admitted schemas and use host big integers:

```text
add(0,y) = y                  add(succ(x),y) = succ(add(x,y))
mul(0,y) = 0                  mul(succ(x),y) = add(y,mul(x,y))
factorial(0) = 1              factorial(succ(x)) = mul(succ(x),factorial(x))
```

The recursive call and unchanged arguments must occur as shown; for
`mul`, the two arguments to the recognized addition may be swapped. The nested
`add` or `mul` must itself pass recognition. Any near miss uses the general
equation interpreter. Optimized factorial must still spend/check fuel per loop
iteration. Exhaustion rejects.

A checker may also take the library's descent-by-ones operators in one
big-integer step, but only on natural arguments, only after the named
definition and every helper it uses have matched their admitted equations
exactly (names, parameters, patterns, and bodies), and only when every name
in the operator's fixed dependency list is in the allow-list. A recognized
shortcut records that whole fixed list, whatever the arguments are, so the
certificate names the same definitions in every implementation:

```text
Grace.Core.Nat.Rec.predecessor              [predecessor]
Grace.Cumulus.Nat.Subtraction.sub           [sub, predecessor]
Grace.Cumulus.Nat.Mod.mod                   [mod, nextRemainder, chooseNat, equalNat,
                                             isZero, predecessor, BoolOps.not, BoolOps.and]
Grace.Cumulus.Nat.Division.quotientNat      [quotientNat] + the list of mod
Grace.Cumulus.Nat.Mod.equalNat              [equalNat, isZero, predecessor, BoolOps.not, BoolOps.and]
Grace.Cumulus.Rat.Computable.RationalCellOps.less
                                            [less, isZero, predecessor, BoolOps.not, BoolOps.and]
Grace.Cumulus.Rat.Computable.RationalCellOps.minus
                                            [minus, isZero, predecessor, chooseNat]
```

The helpers are the `Grace.Cumulus.Nat.Mod` and `Grace.Core` definitions of
those names. `sub(m, 0)`, `mod(n, 0) = n`, and `quotientNat(n, 0) = 0` take the
shortcut like any other arguments. A certificate whose allow-list lacks any
name in the fixed list is checked by the general interpreter instead, which
records exactly the definitions it unfolds; both certificates are valid.

## 8. Linked theorem boundaries

The main proof root and **every** named theorem boundary must have an empty
assumption context. Reject any open root or boundary before allowing an
opcode-2 citation or theorem admission. A local derivation `A ⊢ A` is not a
closed theorem. This condition applies equally to standalone G17M and G17M
batches embedded in G17C.

A linked module lists `(theorem-name, root-instruction)` boundaries. At the end,
the result at each root must equal that theorem's statement in the environment.

If opcode 2 names a theorem that also has a boundary in this tape, it may use
only a boundary whose root instruction is earlier than the current
instruction. Reject self-reference and forward theorem reference. Theorem
statements in the environment are goals; they are no permission to assume the
theorems being checked.

An unlinked tape has no boundary list. In that low-level form, every theorem
named by opcode 2 is external and trusted. Portable release checking should use
linked tapes.

## 9. Minimal checker loop

```text
read and authenticate environment
read and authenticate G17M
reject unless environment digests match
validate symbols, arenas, signatures, contexts, roots, and premise topology
results = ∅ array
for pc from 0 through code.length-1:
    instruction = code[pc]
    reject every premise >= pc
    derived = apply_primitive_rule(instruction, results, environment)
    reject unless derived == instruction.claimed_formula
    results[pc] = derived
check every theorem boundary
accept
```

Acceptance is the only security-sensitive output. Diagnostics, pretty
printing, caching, and benchmarking cannot change it.

## 10. Conformance commands

The checked-in `conformance/manifest.json` is the portable test index for this
specification. Each entry supplies an expected accept/reject result and SHA-256
checksum for a G17M tape; the manifest also authenticates its shared G17ENV.
Corpus checking must consume these fixed bytes. Regenerating vectors with the
TypeScript proof producer is a separate maintainer operation and is not an
independent conformance check.

Run both included implementations over all vectors:

```sh
npm run conformance
npm run conformance:python
```

See `conformance.md` for manifest fields, present coverage, and limitations.

For an individual source module, generate a tape and its environment:

```sh
node bin/g17.ts compile examples/Arithmetic.g17 \
  --out Arithmetic.g17m --environment Arithmetic.g17env
```

Check it with the TypeScript checker:

```sh
node bin/g17.ts verify-machine examples/Arithmetic.g17 \
  --machine Arithmetic.g17m
```

Check the same bytes with the independent Python checker:

```sh
python3 checkers/python/g17check.py Arithmetic.g17m \
  --environment Arithmetic.g17env
```

The test suite generates arithmetic, set-theory, computation, classical-logic,
existential, datatype-induction, and well-founded-induction tapes; requires the
TypeScript and Python implementations to accept them; and requires both digest
and environment mutations to be rejected.

## In-process checker cache boundary

Caching is an implementation optimization and may not change a proof's
conclusion or required context. Closed checks must not inherit tokens from
caller-owned arrays that were previously nonempty. In the TypeScript API, an
assumptions array remains caller-owned and its entries may be replaced or
removed between calls; the checker detects these changes. Formula objects
retained in a context snapshot are deeply frozen, like retained proof
certificates, so their identities cannot change meaning. A shallow-frozen outer
object alone is insufficient.

These requirements do not introduce any proof-format opcode or logical rule.
The mutable-context regressions are in `tests/evidence-checking.test.ts`.

## Admission and cache retention

Freeze caller-owned statements and retained declaration data before admission.
Freeze successful child proofs and their conclusions before caching them,
including children of a parent whose eventual check fails. A shallow-frozen
machine program is not evidence that its nested arena arrays are immutable;
establish deep immutability before reusing a cached arena.

The independent Python, OCaml, and Rust checkers each cover all 30 G17M
opcodes and the current G17C v3 admission operations, including exact
computation and independent foundation construction. See `checkers/README.md`.
