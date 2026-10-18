# Small-step semantics of the proof checker

This page states what a Grace17 proof checker computes, as a transition
system over explicit states. It is the specification the independent
checkers implement, and it is deliberately free of implementation detail:
no file formats, no data structures, no optimizations. The byte-level
encodings are in the [kernel format](kernel-format.md) and the
[compiled module format](compiled-module-format.md); the construction of the
foundation is in [foundation bootstrap](foundation-bootstrap.md). Where
those pages and this one appear to disagree, the disagreement is a bug to be
reported, and the more restrictive reading is the one to implement.

A checker has one security-relevant output: **accept** or **reject**. Every
transition below is total in the sense that a state either steps to a
successor or is stuck, and a stuck state rejects. Nothing is ever repaired,
defaulted, or skipped.

## 1. Objects

**Symbols** are nonempty strings of Unicode scalar values.

**Terms** `t` are built from free variables `x` (a symbol), bound variables
`#i` (a de Bruijn index, `#0` the nearest enclosing binder), applications
`f(t₁, …, tₙ)` of a function symbol, and natural literals `n`. The literal `n`
is the same term as `succ` applied `n` times to `zero()`; a checker folds
`zero()` to `0` and `succ(n)` to `n + 1` whenever it constructs a term, so
the two spellings never coexist.

**Formulas** `A` are `⊥`, equations `s = t`, predicate applications
`P(t₁, …, tₙ)`, implications `A → B`, conjunctions `A ∧ B`, disjunctions
`A ∨ B`, equivalences `A ↔ B`, and the quantifiers `∀ A` and `∃ A`, whose
bound variable is `#0` inside `A`. Negation is `A → ⊥`. Two formulas are the
same when they are structurally identical; because binders are nameless, this
is α-equivalence.

**Contexts** `Γ` are finite ordered sequences of formulas. `Γ, A` is `Γ`
extended with `A` at the end. Order is significant: the rules below compare
contexts by equality of sequences.

An **environment** `E` is a record with these components:

| Component | Content |
|---|---|
| `caps` | the foundation profile and its capability flags: `separation`, `replacement`, `choice`, `globalChoice`, inductive definitions |
| `fun` | a finite map from function symbols to arities |
| `pred` | a finite map from predicate symbols to arities |
| `ax` | a finite map from axiom names to closed formulas |
| `thm` | a finite map from theorem names to closed formulas |
| `def` | a finite map from definition names to records of kind, parameters, and named property formulas |
| `data` | a finite map from datatype names to their constructor records |
| `rec` | a finite map from recursive function names to their admitted equations and termination data |
| `body` | a finite map from explicitly defined function names to their parameters and body terms |

A term is **well-signed** in `E` when every application `f(t₁, …, tₙ)` has
`fun(f) = n`; a formula is well-signed when its terms are and every
`P(t₁, …, tₙ)` has `pred(P) = n`. A formula is **closed** when it has no free
variable. The digest `⌈E⌉` of an environment is the SHA-256 of its canonical
serialization, defined in the kernel format; two environments are the same
exactly when their digests agree, and the digest is order-free in every
component.

The binding operations are specified in section 5. They are the only
operations on terms and formulas that a checker needs.

## 2. Judgments and the result table

The checker establishes judgments of the form

```text
E ; Γ ⊢ A
```

read "in environment `E`, under assumptions `Γ`, the formula `A` is derived".
A proof is a finite sequence of instructions; instruction `i` claims a
judgment `Γᵢ ⊢ Aᵢ` and names earlier instructions as its premises. The
checker maintains a **result table** `R`, a partial map from instruction
indices to judgments. `R(j) = (Γⱼ ⊢ Aⱼ)` means instruction `j` has been
checked.

## 3. The proof machine

### State

A machine state is a tuple

```text
⟨E, P, pc, R⟩
```

where `E` is the environment, `P` the program (symbol table, term arena,
formula arena, context arena, instruction sequence `code`, root instruction,
and theorem boundaries), `pc` the index of the next instruction, and `R` the
result table. The initial state is `⟨E, P, 0, ∅⟩`.

### Static validation

Before the first step, the program must satisfy every condition below. A
violation rejects without stepping.

- The environment named by the program is `E`: its digest equals `⌈E⌉`.
  (Inside a compiled module the environment is the live one produced by the
  preceding events, and this condition is replaced by the module's digests;
  see section 7.)
- Every arena is an intern table: no duplicate symbol, term, formula, or
  context, and no empty symbol. Every term child refers to an earlier term
  node; every formula child refers to an earlier formula node.
- Every application node is well-signed in `E`.
- Every context is a sequence of formula indices.
- Every instruction has the shape `[op, claim, context, k, p₁ … pₖ, data…]`
  with `op` in `0 … 29`, `claim` a formula index, `context` a context index,
  every premise `pⱼ < pc` of the instruction, and exactly the rule-data words
  the opcode requires.
- The root instruction and every theorem-boundary root have the empty
  context.

### Step

The step relation is

```text
⟨E, P, pc, R⟩  ⟶  ⟨E, P, pc + 1, R[pc ↦ (Γ ⊢ A)]⟩
```

when `code[pc]` has context `Γ`, the rule for its opcode derives the formula
`A` from the premises' entries in `R` with the rule's side conditions
satisfied, and `A` is the instruction's claimed formula. If no rule applies,
or the derived formula differs from the claim, the state is stuck and the
checker rejects. Unless a rule says otherwise, every premise must have the
same context `Γ` as the instruction.

The machine terminates when `pc = |code|`. In the terminal state the
boundary conditions of section 6 are checked, and the checker accepts.

### Rules

In each rule, `pᵢ` names a premise instruction and `R(pᵢ) = (Γ ⊢ Bᵢ)`. The
data words follow the premises.

**Hypotheses and the environment.**

```text
(0) assumption        data A           ⟹  A              when A ∈ Γ
(1) axiom             data name        ⟹  ax(name)
(2) theorem           data name        ⟹  thm(name)      or the statement of an earlier
                                                           checked boundary named name
(3) definition        data name, prop  ⟹  def(name).prop
```

Rule 2 inside a linked tape may cite a boundary only when that boundary's
root instruction is earlier than `pc`. A theorem being proved is never
available to its own proof or to a later proof in the same tape.

**Equality.**

```text
(4) reflexivity       data t                         ⟹  t = t
(5) symmetry          p₁ : a = b                     ⟹  b = a
(6) transitivity      p₁ : a = b,  p₂ : b = c        ⟹  a = c
(7) congruence        p₁ : a₁ = b₁ … pₙ : aₙ = bₙ, data f   ⟹  f(a₁…aₙ) = f(b₁…bₙ)
                                                        when fun(f) = n
(13) equality elimination
                      p₁ : a = b,  p₂ : M[x := a],  data x, M, r
                                                    ⟹  M[x := b]
```

In rule 13 the motive `M` is a formula with the free variable `x`, and
`M[x := t]` is free substitution. With reverse flag `r = 1` the roles of `a`
and `b` are exchanged: the second premise is `M[x := b]` and the result is
`M[x := a]`. The premise formula is compared after substitution, so the
checker never guesses which occurrences were rewritten.

**Implication and quantifiers.**

```text
(8) → introduction    p₁ in context Γ, A : B,  data A   ⟹  A → B      in context Γ
(9) → elimination     p₁ : A → B,  p₂ : A              ⟹  B
(10) ∀ introduction   p₁ : A,  data x                   ⟹  ∀ (abstract x in A)
                                                        when x is not free in Γ
(11) ∀ elimination    p₁ : ∀ A,  data t                 ⟹  instantiate A at t
(23) ∃ introduction   p₁ : A[x := t],  data x, A, t     ⟹  ∃ (abstract x in A)
(24) ∃ elimination    p₁ : ∃ A,  p₂ in context Γ, A[w] : C,  data w
                                                        ⟹  C
                                                        when w is fresh for Γ, ∃ A, and C
```

In rule 24, `A[w]` is the body `A` instantiated at the free variable `w`.
Freshness means `w` does not occur free in any formula of `Γ`, in the
existential premise, or in the conclusion `C`.

**Propositional connectives.**

```text
(14) ∧ introduction   p₁ : A,  p₂ : B         ⟹  A ∧ B
(15) ∧ left           p₁ : A ∧ B              ⟹  A
(16) ∧ right          p₁ : A ∧ B              ⟹  B
(17) ∨ left           p₁ : A,  data B         ⟹  A ∨ B
(18) ∨ right          p₁ : B,  data A         ⟹  A ∨ B
(19) ∨ elimination    p₁ : A ∨ B,  p₂ in Γ, A : C,  p₃ in Γ, B : C   ⟹  C
(20) ↔ introduction   p₁ : A → B,  p₂ : B → A ⟹  A ↔ B
(21) ↔ forward        p₁ : A ↔ B              ⟹  A → B
(22) ↔ backward       p₁ : A ↔ B              ⟹  B → A
(25) ⊥ elimination    p₁ : ⊥,  data C         ⟹  C
(26) double negation  p₁ : (A → ⊥) → ⊥,  data A   ⟹  A
```

Rule 26 is the only classical rule. The logic is classical first-order
logic with equality; there is no other source of excluded middle.

**Induction.**

```text
(12) datatype induction
     data D, x, M, params…, cases…
     one premise per constructor c of D, in context Γ extended as described
     ⟹  ∀ (abstract x in D(params…, x) → M)
```

The parameters are terms that do not contain `x`, and there must be exactly
one case per constructor, in any order. For the case of constructor `c` with
fields `y₁ … yₘ`, all fresh for `Γ`, the parameters, and `M`: for each
recursive field `yⱼ`, the case context is extended with `D(params…, yⱼ)` and
then with `M[x := yⱼ]`; for each parameter field, it is extended with the
field's membership in its selected carrier; the case must derive
`M[x := c(y₁ … yₘ)]`.

```text
(27) well-founded induction
     p₁ : wellFoundedOn(r, d),
     p₂ : ∀ x, x ∈ d → (∀ y, (y ∈ d ∧ relates(r, y, x)) → M[y]) → M[x]
     data r, d, x, y, M
     ⟹  ∀ x, x ∈ d → M[x]
```

Here `x` and `y` are distinct symbols absent from `Γ`, `y` is not free in
`M`, and neither `r` nor `d` contains `x` or `y`.

**Computation.**

```text
(28) ground computation   data n, f₁ … fₙ   ⟹  s = t
(29) rational class computation            ⟹  s = t
```

Rule 28 derives `s = t` for closed terms `s` and `t` whose normal forms, under
the evaluation relation of section 4 restricted to unfolding exactly the
definitions `f₁ … fₙ`, are identical, and where the set of definitions
actually unfolded equals `{f₁ … fₙ}`. The names are distinct and sorted.
Rule 29 derives an equation between two rational class constructors from
the proved quotient criterion of the environment and an exact cross-product
computation; its precise conditions are in the kernel format.

## 4. Evaluation

Ground computation is a normalization relation on closed terms over the
value domain

```text
v ::= n (an arbitrary-precision natural)  |  f(v₁, …, vₙ)
```

Arguments normalize before the application. `zero()` is `0` and `succ(v)` is
`v + 1` when `v` is a natural. An application `f(v₁ … vₙ)` unfolds only when
`f` is in the instruction's allow-list and `f` has an explicit or recursive
definition in `E`:

- an explicit definition binds its parameters to the normalized arguments and
  normalizes its body;
- a recursive definition selects the unique admitted equation whose patterns
  match the arguments, where `zero` matches `0`, `succ(p)` matches a positive
  natural and binds `p` to one less, and any other constructor matches an
  application with that constructor at the head; it then normalizes the
  equation's body under the pattern bindings.

Any other application is a value. Every unfolding is recorded. The relation
is deterministic, and a checker gives it a fuel budget; exhausting the budget
rejects. A checker may replace the unfolding of the admitted schemas for
addition, multiplication, and factorial by host big-integer arithmetic only
after matching the schema's defining equations exactly, as the kernel format
specifies; a near miss uses the general relation.

## 5. Binding operations

Four operations suffice, and each is defined by structural recursion that
tracks the current binder depth `d` (initially `0`, incremented on entering a
quantifier):

- **abstract(x, A)**: replace every free variable `x` by the bound variable
  `#d`; the result is the body of a quantifier binding `x`;
- **instantiate(A, t)**: replace every bound variable `#d` by `t` shifted by
  `d` and decrement every bound index greater than `d`; the result is `A` with
  its outermost binder removed and its variable replaced by `t`;
- **substitute(A, x, t)**: replace every free variable `x` by `t`; bound
  variables are untouched;
- **free(A)**: the set of free-variable symbols of `A`.

Shifting a term by `d` increments every bound index that refers outside the
term by `d`. Every term or formula these operations construct passes through
the same interning as the arenas, including the natural folding of section 1.

## 6. Boundaries

A linked program lists theorem boundaries `(name, root)`. In the terminal
state, for every boundary, `R(root)` must be `∅ ⊢ thm(name)`: the empty
context and exactly the statement recorded for `name` in `E`. The program's
own root must likewise have the empty context. A derivation `A ⊢ A` is a
valid instruction but never a theorem.

An unlinked program has no boundaries, and every theorem it cites by rule 2
is external to it; only linked programs are used for release checking.

## 7. Environment replay

A compiled module is a sequence of events that extend an environment. The
replay machine has states

```text
⟨E, ρ⟩
```

where `ρ` is a finite map from module names to content digests, the
**receipts**. Replay is the only way an environment comes into existence: no
checker ever reads an environment from a file and trusts it.

### Foundation

The initial environment is constructed, never loaded. For a profile `ZF`,
`ZFC`, or `ZFG`, the checker performs the bootstrap stages: install the
primitive signature and the profile's axioms with their capability flags,
install the transparent definitions of the prelude by the ordinary definition
events, register the von Neumann naturals, and seal. The result is `⟨E₀, ∅⟩`,
and `⌈E₀⌉` must equal the foundation digest the module names. A receipt file
for a foundation names only its profile and expected digest; it is not an
environment.

### Events

Each event is a transition `⟨E, ρ⟩ ⟶ ⟨E′, ρ⟩` whose precondition is checked
in `E` and whose effect installs new entries in `E′`. A proof inside an event
is checked by the rules of section 3 against `E`, the environment before the
event, so that nothing can cite itself. In every event the new name must be
fresh in `E`, parameters must be distinct symbols, and every term and formula
must be well-signed in `E`.

```text
declareFunction(f, n)       E′ = E with fun(f) = n
declarePredicate(P, n)      E′ = E with pred(P) = n

defineFunction(f, x̄, t)     free(t) ⊆ x̄ and f ∉ t
                            E′: fun(f) = |x̄|, body(f) = (x̄, t),
                                def(f).equation = ∀ x̄, f(x̄) = t

definePredicate(P, x̄, A)   free(A) ⊆ x̄ and P ∉ A
                            E′: pred(P) = |x̄|, def(P).equation = ∀ x̄, P(x̄) ↔ A

defineSubset(S, x̄, y, b, C) caps.separation; free(b) ⊆ x̄; free(C) ⊆ x̄ ∪ {y}
                            E′: fun(S) = |x̄|, def(S).membership = ∀ x̄ y, y ∈ S(x̄) ↔ (y ∈ b ∧ C)

defineReplacement(F, x̄, d, u, w, A, π)
                            caps.replacement; free(d) ⊆ x̄; free(A) ⊆ x̄ ∪ {u, w};
                            π proves ∀ x̄, ∀ u, u ∈ d → ∃ w, A ∧ ∀ w′, A[w := w′] → w′ = w
                            E′: fun(F) = |x̄|, def(F).functionality = that formula,
                                def(F).membership = ∀ x̄ m, m ∈ F(x̄) ↔ ∃ u, u ∈ d ∧ A[w := m]

reifyUnaryOperation(G, g, d, c, x, π)
                            caps.replacement; fun(g) = 1; d and c closed;
                            π proves ∀ x, x ∈ d → g(x) ∈ c
                            E′: fun(G) = 0, def(G).membership = ∀ p, p ∈ G ↔ ∃ x, x ∈ d ∧ p = (x, g(x)),
                                def(G).functionOn = functionOn(G, d, c),
                                def(G).application = ∀ x, x ∈ d → apply(G, x) = g(x)

defineUniqueFunction(f, x̄, y, A, π)
                            y ∉ x̄; free(A) ⊆ x̄ ∪ {y};
                            π proves ∀ x̄, ∃ y, A ∧ ∀ y′, A[y := y′] → y′ = y
                            E′: fun(f) = |x̄|, def(f).existsUnique = that formula,
                                def(f).characterization = ∀ x̄, A[y := f(x̄)]

declareDatatype(D, …)       fresh constructor names, distinct parameters, disjoint
                            recursive-field and parameter-field indices
                            E′: data(D) installed; pred(D) and fun(c) for each constructor;
                                def(D) records each constructor's introduction law,
                                exhaustive cases, constructor injectivity, pairwise
                                disjointness, and, for a surface datatype, the tagged
                                Kuratowski encoding of each constructor

registerNaturalDatatype()   E′: the built-in von Neumann naturals are registered as a
                            datatype; no proposition is added

defineStructuralFunction(f, x̄, D, k, eqs)
                            exactly one equation per constructor of D, matching only
                            parameter k, with linear patterns and every recursive call
                            on a variable bound by a recursive field of the matched
                            constructor; every other symbol in a body is well-signed
                            E′: fun(f) = |x̄|, rec(f) installed,
                                def(f).equation.i = ∀ (pattern variables), f(patterns) = body

defineWellFoundedFunction(f, x̄, D, k, eqs, r, d, μ, π₁, π₂, π̄)
                            coverage as for structural recursion; r and d closed;
                            free(μ) ⊆ x̄; π₁ proves wellFoundedOn(r, d);
                            π₂ proves ∀ x̄, μ ∈ d; for the j-th recursive call f(ā)
                            in an equation with pattern variables ȳ, πⱼ proves
                            ∀ ȳ, relates(r, μ[x̄ := ā], μ[x̄ := patterns])
                            E′: fun(f) = |x̄|, rec(f) installed with its termination data,
                                def(f) records every equation and every obligation

defineWellFoundedSetFunction(…), defineMembershipRecursiveFunction(…),
defineTransfiniteFunction(…)
                            Replacement-backed recursion over a proved well-founded
                            relation, over membership under Foundation, and over the
                            ordinals; each checks its well-foundedness or Foundation
                            requirement, the shape of its step, and for transfinite
                            recursion the canonical successor and ordinal interfaces;
                            each installs a non-executing function with its
                            history-membership and defining-equation properties

addTheorem(name, A, π)      A closed; π proves ∅ ⊢ A in E
                            E′: thm(name) = A

theoremBatch(statements, program)
                            the program of section 3 runs against E with every statement
                            as a boundary; the batch is atomic
                            E′: thm(name) = A for every (name, A) in the batch
```

The exact fields of each event are those of the same-named operation of the
reference kernel, and a checker must redo every check listed; copying a
property from the file is never acceptable. An unknown event rejects. No
event adds an axiom: foundational strength enters only through the
foundation construction.

### Modules

A module names its foundation, its complete dependency closure in replay
order, the expected digest `⌈E⌉` after foundation and dependencies, its
events, and the expected digest after its events. Replaying a module from
`⟨E₀, ∅⟩`:

1. for each dependency `(m, δ)` in order, replay the artifact for `m` by this
   same procedure and require its content digest to be `δ` and its receipt to
   be recorded, `ρ(m) = δ`;
2. require `⌈E⌉ = baseEnvironment`;
3. apply the module's events in order;
4. require `⌈E⌉ = resultEnvironment`, and record `ρ(module) = ` the
   module's content digest.

A stale, missing, reordered, or differently compiled dependency therefore
fails at step 2, before the first local event. Receipts record provenance
only; no rule of section 3 consults them, and they do not enter `⌈E⌉`.

## 8. Acceptance

The checker accepts exactly when every transition it attempted succeeded
and every terminal condition held: the proof machine reached the end of its
program with every boundary satisfied, or the replay machine reached the
final digest. Every other outcome, including a resource limit, a malformed
encoding, an unknown opcode or event, a digest mismatch, and an internal
error, is a rejection. There is no partial acceptance and no fallback to
another checker.

## 9. Implementations

The TypeScript kernel in `src/kernel.ts` implements these rules on named
abstract syntax; its proof-machine form is `src/machine.ts`, and the
compiled-module replay is `src/compiled-module.ts`. The independent checkers
in `checkers/` implement the same relation from this page and the format
pages, in Python, OCaml, and Rust, sharing no code with the kernel or with
each other. The [conformance corpus](conformance.md) exercises every opcode
of section 3 with one accepted and one rejected tape, and every checker must
agree on all of them.
