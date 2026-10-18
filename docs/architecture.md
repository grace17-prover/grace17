# Architecture

This document describes how Grace17 is put together: what is trusted, how
proofs are represented and replayed, how computation is admitted, and how the
surface language elaborates to kernel inferences. It is written for people who
want to work on the system itself. For the mathematics, start with the
[introduction](introduction.md); for the checker contract, see the
[kernel format](kernel-format.md).

## Trust boundary

The trusted seed consists of the AST well-formedness checks, the proof-rule
checker, the definition-event validators, and the listed foundational axioms
and capabilities. It also includes compact-natural canonicalization and the
ground evaluator behind the primitive `compute` rule, with its arithmetic-schema
recognition and host `bigint` operations. Tactics and agent integrations
produce proofs or extension certificates, and this layer checks them.

`defineFunction` and `definePredicate` are conservative explicit definitions.
`defineSubset`, `defineReplacement`, and `reifyUnaryOperation` are marked as
uses of Separation or Replacement, so an audit can tell a set-existence
principle from an abbreviation. `foundationReport()` lists the active profile,
named axioms, and every schema instance deterministically. The surface image
comprehension `{ f(x) | x in A }` elaborates to `defineReplacement` with a
kernel-checked equality functionality certificate.

Set-membership induction is outside the trusted rule set. The tactic
`induction x using membership` uses the library's Replacement-built transitive
closure of `x`, proves restricted membership well-founded from
`set.foundation`, and emits opcode-27 well-founded induction, so the
TypeScript kernel and the independent checkers all see the complete derivation.

The same checked rule is available for any certified relation when the goal
has shape `∀ x, x ∈ A → P(x)`:

```g17
induction x over A ordered by r certified by founded
intro x
intro hx
intro ih
```

Here `founded` proves `wellFoundedOn(r, A)`, and `ih` supplies `P(y)` for every
`y ∈ A` with `relates(r, y, x)`. The command is an elaborator tactic; the
kernel has no rule for it.

Set-sized noncomputable recursion over a proved well-founded relation names
its certificate:

```g17
noncomputable well-founded def rankOn (A x : Set) : Set
  over A ordered by membershipOn(A)
  certified by membershipOn.wellFounded
  | x using history => 𝒫(history)
```

The certificate must check as `wellFoundedOn(relation, domain)` uniformly in
the definition's parameters. The generated `rankOn.history.membership` and
`rankOn.equation.direct` properties expose the predecessor/value graph and the
defining equation to later proofs. The function is non-executable; the event
is the conservative Foundation-and-Replacement recursion theorem.

`defineWellFoundedFunction` does not trust a termination tactic. It checks a
proof that a set relation is well-founded, a universally quantified proof that
the measure lands in its domain, and a decrease proof synthesized for each
recursive call. Then the defining equations are registered and made
executable.

## Ordinal termination

`../src/ordinal.ts` is the computational side of the ordinal design. It
implements normalized hereditary Cantor forms below epsilon_0, executable
comparison, and replayable comparison certificates. These TypeScript values
are notation objects. The intended bridge maps them to von Neumann ordinals and
proves that executable comparison agrees with membership.

The ZFG seed includes Foundation, defines `relates(r,x,y)` by ordered-pair
membership, and defines `wellFoundedOn` by the least-element property.
`Grace.Bootstrap` constructs `epsilon0.less` by Separation and proves that it is
membership restricted to `epsilon0`. Neither fact is an axiom. The proof that
this restriction is well-founded is also not an axiom; it belongs in the
bootstrapped theorem library as a derivation from Foundation.

`epsilon0` is the set/notation system and `epsilon0.less` is its strict order;
structural definitions never mention it.

## Run

Node 24 can execute the TypeScript source directly:

```sh
npm test
npm run demo
npm run proofs
npm run machine
npm run compute
npm run bench:machine
npm run arithmetic
npm run scaling
npm run check:g17
npm run workbench
```

`npm run workbench` serves the local Grace17 proof laboratory at
`http://127.0.0.1:1717`. Press Ctrl/⌘ + Enter to check the editor buffer.
The workspace also checks automatically after edits. Open several `.g17` files
at once, or drag them into the editor, and their imports are resolved together.
Each tab checks independently with its transitive imports while every open
buffer remains available as a module override; errors in other tabs do not
hide the active tab's theorem information or steal editor focus.
Move the cursor through a tactic proof to follow its goal state. An annotated
proof gets a collapsible **Proof map** whose landmarks track the cursor. Expand
a landmark to browse its checked tactics, remaining goal counts, and source
locations. `exact?`, `apply?`, and `rw?` open an **Info** drawer with the
checked proof-search results; move onto an `eval` line to see its normal form
and reduction count; expand **Kernel proof** to read the checked certificate
as a Fitch-style derivation. Its numbered lines cite prior premises, draw
nested assumption scopes, and show the kernel arguments on selection. A
draggable horizontal handle lets the derivation take over most of the proof
pane.

The editor expands backslash commands when followed by Space, Tab, or Enter:
`\forall` gives `∀`, `\exists` gives `∃`, `\in` gives `∈`, `\to` or `\r`
gives `→`, and `\l` gives `←` (for example, `rw ← h`). The **Symbols** menu
lists the common spellings; `\<` and `\>` give the pattern brackets `⟨` and
`⟩`; `\powerset`, `\cup`, `\cap`, `\setminus`, and `\times` give `𝒫`,
`∪`, `∩`, `∖`, and `×`; and `\simeq` and `\mapsto` give `≃` and `↦`. Greek names such
as `\alpha` and relations such as `\le` are supported
too. Destructuring does not require Unicode: `rcases h with (left, right)` and
`obtain (x, hx) := h` are equivalent to their `⟨...⟩` forms.

Or invoke the checker directly:

```sh
node bin/g17.ts check examples/Arithmetic.g17 examples/Sets.g17 examples/Unicode.g17
node bin/g17.ts check --foundation ZF examples/Sets.g17
node bin/g17.ts check --json examples/Arithmetic.g17 examples/Sets.g17 examples/Unicode.g17
node bin/g17.ts export examples/Sets.g17 --theorem pair.left --out pair-left.g17proof.json
node bin/g17.ts view examples/Sets.g17 --theorem pair.left --out pair-left.html
```

Library modules compile once into per-module artifacts and replay afterwards,
so checking a file over a large import closure takes well under a second:

```sh
node bin/g17.ts build --module-root lib --artifacts build/modules lib/Grace/Cumulus.g17
node bin/g17.ts check --module-root lib --artifacts build/modules examples/Introduction.g17
```

`build` rebuilds only modules whose source or import closure changed; `check
--artifacts` builds what it needs first. See the
[compiled module format](compiled-module-format.md) for what an artifact
contains and how it is checked.

## Modules and namespaces

Modules set dependency boundaries; namespaces organize names and mean nothing
to the kernel:

```text
module Grace.Examples.Compute
import Grace.Core.Nat
open Grace.Core.Nat.Rec

namespace Demo
def double (n : Nat) -> Nat
  | zero => zero
  | succ(n) => succ(succ(double(n)))
end Demo
```

Every module opens its own namespace implicitly, so the environment stores
`double` as `Grace.Examples.Compute.Demo.double`; its source module is recorded
separately. Reopening `namespace Demo` inside that module extends that same
namespace, and moving a declaration to another module renames it, because the
module name is part of the name. Unqualified references search the current
namespace, its parents, opened imported namespaces, and finally root names.
Two matching opened names are an error whatever the import order; qualify the
name to choose. A `_root_.` prefix bypasses relative lookup, and
`namespace _root_.Shared` declares a namespace at the root that several
modules may extend; Cumulus keeps every declaration inside the namespace of
its own module instead. An `open` of a foreign namespace is rejected unless
its module was imported. `moduleReport()` exposes the resulting dependency
graph to agents.

Library entrypoints may declare `export open Namespace`. These opens compose
through later entrypoints, while a plain `open` stays local. A new development
can begin with `import Grace.Cumulus.Main`, or with one subject entrypoint such
as `import Grace.Cumulus.NumberTheory`.

`loadModuleGraph` and `g17 --module-root <dir>` resolve `Grace.Core.Nat` as
`Grace/Core/Nat.g17`, recursively discover imports, reject dependency cycles,
and elaborate modules in topological order. Thus a CLI invocation needs only
the entry module:

```sh
g17 check --module-root lib examples/Compute.g17
g17 run --module-root lib examples/Compute.g17 \
  --function Grace.Examples.Compute.Demo.double --args 100000
```

## Core computation and Cumulus set theory

`Grace.Core` is the small computation bootstrap. Reusable set mathematics is
organized under `Grace.Cumulus.Set`; both live beneath the sole module root
`lib/`. Their definitions use the same source language as downstream users:

```text
module Grace.Cumulus.Set.Basic

def singleton (x : Set) : Set := pair(x, x)
def intersection (A B : Set) : Set := { x in A | x in B }
predicate Subset (A B : Set) := forall x, x in A -> x in B

theorem intersection.subset_left (A B : Set)
  shows Subset(intersection(A, B), A)
proof
  settle with Subset, intersection
```

A `def` is a conservative abbreviation. A bounded comprehension is admitted
as a Separation instance and appears in the foundation audit. Predicate
definitions are conservative and unfold through checked equivalence. `settle`
can unfold these definitions inside atomic membership goals using equality
elimination, decompose assumptions, forward-chain equivalences, and synthesize
bounded witnesses, and every successful step elaborates to kernel inferences.

The same `def` keyword also introduces checked equation-style programs. Syntax
determines the elaboration route: `:=` gives an explicit definition, while
`| pattern => body` clauses give exhaustive pattern matching and structural
recursion. Predicate, class, explicit-definition, and equation bodies may span
physical lines; the parser joins the declaration until the next declaration or
equation boundary. The older `define` spelling is accepted as an alias; use `def`.

`Grace.Cumulus.Set.Finite` is an early automation stress test. Its union and
insertion proofs require `settle` to eliminate existential witnesses from the
Union axiom, split pair-membership disjunctions, and transport membership over
the resulting equalities. The search happens in the tactic; the certificates
contain `existsElim`, `orElim`, and `eqElim` nodes for the kernel to replay.

The computational half is executable:

```text
def factorial (n : Nat) -> Nat
  | zero => succ(zero)
  | succ(n) => mul(succ(n), factorial(n))
```

Check the whole dependency graph or call the admitted function directly:

```sh
g17 check --module-root lib lib/Grace/Core.g17
g17 run --module-root lib lib/Grace/Core.g17 \
  --function Grace.Core.Nat.Rec.factorial --args 20
```

## Fast and certified computation

`evaluate` and `evaluateFast` execute only admitted defining equations and do not allocate
a proof tree per reduction. `evaluateCertified` follows the same equations but
also emits an equality proof for independent kernel replay. The fast path uses
identity memoization over immutable term DAGs and preserves constructor nodes
when their children are already normal. `evaluateFastWithStats` reports calls,
equation reductions, and cache hits.

This is the ACL2 separation: logical admission determines which programs may
run, routine execution is lean, and proof-producing evaluation is available
when a portable computation certificate is required.

`evaluateNative` and `callNative(kernel, name, args)` bypass unary constructor
trees entirely: natural values are JavaScript `bigint`s, so they have no fixed
machine-word overflow, while other values are compact constructor/application
DAGs. The evaluator executes admitted explicit definitions and general
recursive equations. It recognizes exact admitted equation schemas for
addition, multiplication, and factorial and uses native `+`, `*`, and an
iterative factorial only after matching those schemas. The library's
descent-by-ones operators (predecessor, truncated subtraction, remainder,
quotient, and the natural equality, order, and subtraction decisions) are
likewise one big-integer step each once their exact equations and helpers
have matched, and each records a fixed dependency list that the reference
checkers share. A near miss falls back to the general interpreter. Direct evaluation returns a value. The kernel
invokes the same evaluator as trusted replay only for `compute`.

## Stepwise tactic proofs

Theorem clauses may use horizontal or layout-oriented notation interchangeably:

```text
lemma combine (a b c : Set)
  requires
    hab : a = b
  shows
    a = b
    ∧
    c = c
proof
  constructor
  . exact hab
  . rfl
```

The body of `requires` or `shows` must be indented farther than its marker. A
new clause or `proof` at the marker indentation ends the formula.

Proofs are written as goal transformations and elaborate to the primitive
proof terms the kernel accepts. Here is `pair.left` written out step by step:

```text
theorem pair.left (x y : Set)
  shows x in pair(x, y)
proof
  have membership := pair.membership at x, y, x
  apply membership.backward
  left
  reflexivity
```

`have ... at ...` instantiates universal propositions; `.forward` and
`.backward` select a direction of an equivalence. `apply` focuses its premises
as new goals. The tactic vocabulary also includes `intro`, `exact`,
`assumption`, `left`, `right`, `constructor`/`split`, `witness`/`use`,
conjunction and disjunction `cases`, `exfalso`, `by_contra`, `contradiction`,
`clear`, `rename`, `revert`, `reflexivity`/`rfl`, `compute`, and
`settle with ...`. Multiple premises become ordered focused goals, and an
unfinished script reports the next goal with its source line.

For a proposition that needs its own derivation, `have h : P` opens an
indented local proof block. After the block closes, `h` is available to the
surrounding proof; nesting follows the same indentation rule. This is separate
from `have h := existing-proof`, which binds a proof already in the checked
environment.

The query tactics perform bounded deterministic search over the imported
environment. `exact?` finds a checked fact that closes the goal, `apply?` finds
a theorem whose conclusion matches and exposes its premises as subgoals, and
`rw?` finds a local or imported equality that changes the goal. The kernel
replays the chosen proof like any handwritten tactic application.

You can declare deterministic macros such as
`tactic solve(rule) := settle with $rule`. See [tactics.md](tactics.md) for
every tactic.

Tactics are elaborator conveniences. The four-line proof above becomes three
universal eliminations, equivalence elimination, disjunction introduction,
reflexivity, implication elimination, and two universal introductions before
kernel admission.

## Proof export and visualization

The kernel retains each admitted theorem's checked certificate. `exportTheorem`
packages that certificate as `grace17.proof` version 4 with:

- the theorem statement and theorem name;
- the exact environment digest;
- a deterministic, hash-consed proof DAG and its digest;
- a context-sensitive trace of the intermediate formula established at every
  rule application, together with its active assumptions and premise links;
- the source tactic commands and their before/after focused-goal states;
- the transitive axiom, theorem, and definition dependency sets;
- an envelope digest binding all of the above.

`verifyExportedProof` checks the envelope and environment, validates the DAG's
digest and backward-only topology, replays every primitive inference, and
compares the derived formula with both the exported and registered statements.
It also regenerates and compares the judgment trace, so a certificate cannot
misreport an intermediate goal even if its envelope digest is recomputed. JSON
serialization and parsing preserve verifiability.

`g17 view` renders the same export as a dependency-free HTML proof explorer.
Its primary view follows the proof script you wrote, showing the focused goal
and local facts after every tactic. A collapsed “Drill into kernel proof”
section exposes the primitive inference tree, where every node shows its active
context, established formula, and premises. It also includes links for shared
judgments, raw kernel data, and the environment and envelope hashes. Example
outputs are `../examples/pair-left-judgments.html` and
`../examples/membership-identity.*`; the latter shows assumption introduction
and discharge clearly.

For compact machine transport, `g17 compile` links every theorem from the
supplied source modules into one shared-arena instruction stream and writes a
`.g17m` file. `g17 verify-machine` reloads the source environment, authenticates
and structurally validates the binary, replays the tape once, and checks every
named theorem boundary:

```sh
node bin/g17.ts compile examples/Sets.g17 --out examples/Sets.g17m \
  --environment examples/Sets.g17env
node bin/g17.ts verify-machine examples/Sets.g17 --machine examples/Sets.g17m
python3 checkers/python/g17check.py examples/Sets.g17m \
  --environment examples/Sets.g17env
```

The OCaml and Rust checkers take the same arguments (`build/ocaml/g17check`,
`build/rust/g17check`); see [the checkers](../checkers/README.md).

The checked `Sets.g17m` example contains seven theorems and 41 numeric
instructions in 978 bytes. `G17M` uses canonical unsigned LEB128 vectors,
UTF-8 symbols, a versioned header, an embedded environment SHA-256 digest, and
a trailing file SHA-256 digest. Its decoder
rejects noncanonical integers, invalid UTF-8, oversized arenas, malformed node
shapes, bad indices, forward proof references, duplicate theorem boundaries,
trailing bytes, and digest corruption before semantic replay. The complete
language-neutral contract is in [kernel-format.md](kernel-format.md); the Python implementation
checks the same bytes without importing any TypeScript code or third-party
package.

## Executable surface language

`../examples/Arithmetic.g17` is parsed, elaborated into primitive proof objects,
and independently checked by the kernel. It defines addition and multiplication
and proves ten facts, including commutativity and right distributivity:

```text fragment
def plus (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(plus(x, y))

theorem plus.commutative (y n : Nat)
  shows n + y = y + n
proof
  induction n
  | zero => settle with plus, plus.right_unit
  | succ(k) using ih => settle with plus, plus.succ_right, ih
```

Constructor cases may contain full tactic scripts:

```text
theorem not.involutive (b : Bool)
  shows not(not(b)) = b
proof
  induction b
  | Bool.false =>
    unfold not
    rfl
  | Bool.true => simp [not]
```

`simp [rules]` performs proof-producing definitional and ground reduction.
`rewrite h`, `rewrite ← h`, and the short `rw` spelling transform the focused
goal and retain an equality-elimination proof for the kernel.

Types in this slice are soft refinements. `Nat` contributes a `Nat(x)` premise;
`Set` denotes the untyped ambient universe and contributes no premise. Thus the
stronger associativity lemma can say `(y z : Set, n : Nat)`: recursion needs
`n` to be natural, while `y` and `z` may be arbitrary sets. Structural
termination is inferred from exhaustive constructor patterns whenever there is
exactly one possible decreasing argument. An explicit `descends x` clause is
available only when inference needs disambiguation.

The Tau engine indexes checked theorems such as
`Nat(x) → Nat(y) → Nat(add(x,y))` as typing signatures. It recursively composes
those signatures, constructor facts, subtype rules, and conjunctions, returning
a kernel proof for every successful inference. The index and inference
algorithm remain outside the trust boundary. `inferSoftTypes`,
`checkSoftType`, and `softTypeReport` expose deterministic APIs for agents;
failed checks return the expected type, inferred predicates, and candidate
rules.

Classes are formulas with a distinguished element variable. An unbounded
comprehension is permitted here because it elaborates to a predicate
definition; no set is constructed:

```text
class Universe (x : Set) := { x | x = x }
class Natural (x : Set) := Nat(x)
class SubsetsOf (A : Class) := { X : Set | forall x, x in X -> x ∈ A }

def naturalsIn (A : Set) : Set := { x in A | x ∈ Natural }

theorem SubsetsOf.Universe
  shows SubsetsOf(Universe) = Universe
proof
  settle with Universe
```

Thus `x ∈ Universe` and `x ∈ Natural` are predicate applications, while
`naturalsIn(A)` is a set obtained by bounded Separation. The element
binder may be written in the class header, as for `Universe`, or inside the
comprehension, as for the parameterized `SubsetsOf(A)`. A `Class` parameter is
a surface-level predicate parameter; a set passed in that position is coerced
to its membership class. Class application substitutes membership formulas,
and class equality elaborates to pointwise equivalence. Consequently the
displayed theorem reaches the kernel as
`forall X, X ∈ SubsetsOf(Universe) <-> X ∈ Universe`. Using a class where a
set term is expected is rejected with a specific diagnostic. This gives
NBG-style class notation conservatively over the one-sorted ZF kernel: classes
quantify over all sets, and are never themselves terms.

The formula language includes equality, membership (`in` or `∈`), predicate
application, `not`, `and`, `or`, `->`, `<->`, `forall`, and `exists`. Explicit
`requires` clauses become checked implication premises and may be named, as in
`requires hab : a ≤ b`. Existential goals use a visible witness:

```text
theorem pair.left (x y : Set)
  shows x ∈ pair(x, y)
proof
  settle with pair.membership

theorem equality.exists_self (x : Set)
  shows exists y, y = x
proof
  witness x => settle
```

Existential assumptions unpack with `obtain`:

```text
unfold LessEqual at hab
obtain ⟨k, hk⟩ := hab
```

For non-equality goals, `settle` performs bounded backward logical search. It
can introduce conjunctions, disjunctions, implications, and universal binders;
instantiate named rules; choose a direction through `↔`; and discharge
reflexive equalities and local premises. Its result is a proof object the
kernel checks.

The grammar is narrow and auditable. Unknown rules, stray lines, malformed
recursion, missing cases, escaping existential witnesses, and failed proof
search are reported with source line numbers.

## Extensible notation

Operator syntax is installed by source declarations; none of it is hardcoded
into the parser:

```text fragment
notation infixl 60 "+" => plus
notation infixl 70 "*" => times
notation infixl 60 "+" => rationalAddValue for Rational
notation infixr 50 "⊕" => append
notation infix 50 "<=" => LessEqual
notation infix 50 ">=" => reverse LessEqual
```

The first two declarations make `x * y + z` elaborate to
`plus(times(x, y), z)`. Precedence is an integer from 0 to 1000; larger values
bind more tightly. `infixl` and `infixr` determine grouping at equal
precedence. `infix` declares a non-associative binary predicate; `reverse`
swaps its arguments, so `x >= y` elaborates to `LessEqual(y, x)`. The target
must be a visible binary function or predicate of the appropriate kind.

The optional `for PredicateName` clause declares a soft-type-directed
implementation of an operator. Several declarations may share the token,
precedence, and associativity when their unary operand predicates are distinct.
The implementation may be direct, or it may come from the proof-producing
instance registry:

```text fragment
notation infixl 60 "+" => call2 via AddOperation(ℚ, _) for Rational
notation numeral "0" via OfNat(ℚ, 0, _) for Rational
```

Tau uses checked unary-predicate evidence to establish the operand type. The
separate `via` query uses the known carrier inputs to synthesize one output
operation or constant and its proof. A mathematical `class` declaration is
neither of these mechanisms. Grace17 erases all notation before kernel
checking. A missing or ambiguous soft type or instance is an error; nothing is
guessed from names or declaration order.

Notation belongs to its declaring module and travels through imports. A local
declaration can override imported notation. If two imports expose incompatible
declarations for the same token, elaboration stops with an ambiguity error
whatever the load order. Multi-character tokens use longest-match
tokenization, and Unicode punctuation needs no separate parser path. Notation
disappears during elaboration: the kernel receives function applications and
predicate atoms.

## Unicode without lock-in

Grace17 accepts mathematical Unicode and plain ASCII as interchangeable
surface notation. Both elaborate to the same kernel syntax.

| Unicode | ASCII | Meaning |
| --- | --- | --- |
| `ℕ` | `Nat` | natural-number soft type |
| `∀ α, P` | `forall a, P` | universal quantification |
| `∃ α, P` | `exists a, P` | existential quantification |
| `¬P` | `not P` | negation |
| `P ∧ Q` | `P and Q` | conjunction |
| `P ∨ Q` | `P or Q` | disjunction |
| `P → Q` | `P -> Q` | implication |
| `P ↔ Q` | `P <-> Q` | equivalence |
| `x ∈ A` | `x in A` | set membership |
| `a ≤ b`, `a < b` | instance-selected checked relation | natural or real order |
| `x ≠ y` | `not (x = y)` | inequality |
| `x + y` | declared with `notation` | conventional addition syntax |
| `x * y` | declared with `notation` | conventional multiplication syntax |
| `A × B` | `product(A,B)` | Cartesian product |
| `ε₀`, `ε₀.less` | `epsilon0`, `epsilon0.less` | ordinal domain and order |
| `⇒` | `=>` | equation or proof-branch result |

Identifiers may use Unicode letters, combining marks, and numeric subscripts.
For example, `../examples/Unicode.g17` defines the recursive function `διπλό`,
proves `διπλό(ν) = ν + ν`, and evaluates `διπλό(4)` to `8` with a certificate.
ASCII works everywhere, for generated modules and minimal toolchains.

## Proof ergonomics

Top-level evaluation is part of the source language, so executable examples
stay beside definitions and proofs:

```text
eval factorial(5)
eval (2 + 3) * 4
```

The checker normalizes each closed term with the admitted evaluator and reports
`120` and `20` respectively. These commands inspect computation without adding
a theorem to the logical environment. Use either `lemma` or `theorem` when the
result should instead be proved and admitted.

Ground equalities have a compact proof form:

```text
theorem times.ground_700
  shows 7 * 100 = 700
proof
  compute
```

`compute` accepts only closed terms. Its proof node stores the source equality
and the sorted allow-list of admitted function definitions used during
normalization, with no unfolding, congruence, or transitivity node per
reduction. During admission and certificate replay, the kernel checks that
allow-list, runs the trusted closed-value evaluator on both sides, and
compares their normal forms. Proof size therefore depends on the statement
and the dependency names, and not on the length of the execution trace or the
size of the answer. Decimal literals occupy one AST node and one numeric-machine
term node and are definitionally equal to their `zero`/`succ` expansion.
Ground naturals are computed with native `bigint` arithmetic; general ground
values are recursively normalized applications. For example,
`7000000000 * 1000000000 = 7000000000000000000` still compiles to one proof
node and one machine instruction. Fuel or host resource exhaustion can only
reject a certificate.

`settle` recursively rewrites with the supplied equations and induction
hypotheses, normalizes both sides of an equality, and emits a primitive proof.
Before returning, it asks the kernel to check the proof it constructed. The
combinators around it are proof-object macros of the same kind.

Rewrite theorems may be conditional. `settle` instantiates their quantified
variables and uses them only when every premise has a checked proof in the
local context or in its explicit `facts` collection. Permutative rules are
oriented by a deterministic term order, so registering commutativity does not
create an endless `a+b -> b+a -> a+b` loop.

Stable collections can be validated once with `prepareRewrites`. Rules are
then indexed by the head symbol of their left side, so normalization does not
scan an entire library at every subterm. Optional `SettleStats` expose terms
visited, candidate rules considered, and successful rewrites for profiling.

## Agent-scale proof transport

`encodeProofDag` converts proof objects to a deterministic postorder DAG and
hash-conses repeated subproofs. This array is also the first Grace17 **proof
tape**: each node is an instruction whose proof operands are backward
references. `checkProofDag` authenticates the tape, rejects forward or cyclic
references, restores saved-result sharing, and checks every distinct
`(instruction, natural-deduction context)` pair once. The checker propagates
context identity itself and never takes it as a cache key from the tape, so
sharing an assumption proof between a valid and an invalid scope cannot bypass
the kernel.

This design takes the useful part of Metamath's verifier model. A finished
proof is data, replay proceeds forward without proof search, and repeated
subproofs are saved instead of expanded. Tactics, rewriting, termination
search, visualization, and elaboration all happen outside this replay loop.
Unlike Metamath, Grace17 keeps structured terms, binders, and
natural-deduction scopes, and the certificate records those contexts.

The numeric representation is a second, independent checker.
`compileProofMachine` alpha-normalizes formulas into de Bruijn form, interns
every symbol and node, topologically orders context-sensitive judgments, and
emits arrays containing integers only. `verifyProofMachine` scans forward and
rejects invalid premise topology, contexts, conclusions, quantifier
instantiations, congruence, computation dependencies, and induction branches. It covers every current
primitive proof opcode: assumptions and dependencies; equality; implication,
conjunction, disjunction, and equivalence; universal and existential
quantification; falsity and classical double-negation elimination; structural
induction; and set-sized well-founded induction. The existing AST kernel
remains the reference checker, and tests require both implementations to
derive alpha-equivalent results as well as reject corrupted machine programs.
The numeric machine delegates its single `compute` opcode to the same trusted
closed-value evaluator, so native `bigint` arithmetic is inside the trust
boundary for that opcode. A direct `eval` result admits nothing. G17M version 4
carries the environment digest in
its authenticated header and retains canonical decimal-natural term opcode 3;
the binary validator rejects malformed or noncanonical decimals. Linked
theorem references are acyclic: a theorem on the current tape is available
only after its boundary instruction has already checked.

Structural hostile-input validation and a packed, authenticated binary
encoding are in place; an independent native/Wasm verifier is still required
before it replaces the AST checker as the certificate trust boundary.
`npm run bench:machine` reports reference and machine rates side by side.

The executable surface form is:

```text fragment
theorem plus.associative (y z : Set, n : Nat)
  shows (n + y) + z = n + (y + z)
proof
  induction n
  | zero => settle with plus
  | succ(k) using ih => settle with plus, ih
```

`proof`, `shows`, `using`, and `settle` are the surface language; the
TypeScript proof combinators are what they elaborate to.

## Architectural direction

An executable Grace17 definition produces four connected artifacts:

1. defining equations in the logic;
2. verified executable code;
3. a first-class set-theoretic graph on every set-sized domain;
4. bridge theorems reducing graph application to computation.

`reifyUnaryOperation` is the simplest instance of that design.
`defineStructuralFunction`, `defineWellFoundedFunction`, and
`evaluateCertified` provide two end-to-end recursive computation paths:
structural descent and proof-supplied well-founded descent. Evaluation unfolds
only accepted equations and returns the result with an equality proof for the
kernel to check.
