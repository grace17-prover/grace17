# Grace17 mathematical notation

Grace17 source may use mathematical notation or the underlying kernel-facing
names in any mixture. They elaborate to identical terms and formulas, so
notation never changes what the kernel checks.

| Mathematical source | Underlying source | Workbench input |
|---|---|---|
| `x ∈ A` | `x in A` or `in(x, A)` at the kernel level | `\in` |
| `¬P` | `not P` | `\not` |
| `x ≠ y` | `not x = y` | `\ne` |
| `x ∉ A` | `not x ∈ A` | `\notin` |
| `∅` | `empty` | `\empty` |
| `{x}` | `singleton(x)` | braces |
| `{x, y}` | `pair(x, y)` | braces |
| `{x, y, z}` | `union2(singleton(x), pair(y, z))` | braces |
| `(x, y)` | `orderedPair(x, y)` | keyboard punctuation |
| `x ↦ y` for a function graph entry | `orderedPair(x, y)` | `\mapsto` |
| `⋃ A` | `union(A)` | `\bigcup` |
| `𝒫(A)` | `powerset(A)` | `\powerset` |
| `A ∪ B`, `A ∩ B`, `A ∖ B` | `union2(A, B)`, `intersection(A, B)`, `difference(A, B)` | `\cup`, `\cap`, `\setminus` |
| `A × B` | `product(A, B)` | `\times` |
| `A ⧸ r` | `quotient(A, r)` | `\quot` |
| `⟦x⟧[A, r]` | `equivalenceClass(A, r, x)` | `\llbracket`, `\rrbracket` |
| `ℕ`, `ℤ`, `ℚ`, `ℝ` | `omega`, `integers`, `rationals`, `reals` | `\mathbb{N}`, `\mathbb{Z}`, `\mathbb{Q}`, `\mathbb{R}` |
| `uₙ`, `a₁` | `apply(u, n)`, `apply(a, 1)` | type `u\_n`, `a\_1` |
| `u[n + 1]` | `apply(u, n + 1)` | keyboard punctuation |
| `f(x)`, `identity(ℝ)(x)` | `apply(f, x)`, `apply(identity(ℝ), x)` | keyboard parentheses |
| `op(x, y)` for an operation graph | `call2(op, x, y)`, the value of `op` at the pair `(x, y)` | keyboard parentheses |
| `A ⊆ B` | `Subset(A, B)` | `\subset` or `\subseteq` |
| `f : A → B` | `FunctionBetween(f, A, B)`, a function graph from `A` to `B` | `\to` after a colon |
| `A ⊂ B` | `ProperSubset(A, B)` | `\psubset` |
| `P ∧ Q`, `P ∨ Q` | `P and Q`, `P or Q` | `\and`, `\or` |
| `P ↔ Q` | `P <-> Q` | `\iff` |
| `∀ x, P`, `∃ x, P` | `forall x, P`, `exists x, P` | `\forall`, `\exists` |
| `∃ m n : ℕ, P`, `∀ (f : A → B), P` | typed binders as in a theorem header, with or without the parentheses: `exists m, Nat(m) and exists n, Nat(n) and P` | `\exists`, `\forall` |
| `m + n`, `m * n` for naturals | `add(m, n)`, `mul(m, n)` | keyboard symbols |
| `m ^ n` for naturals | `pow(m, n)` | keyboard symbol |
| `n!` for a natural | `factorial(n)` | keyboard symbol |
| `m - n` for naturals, truncated at 0 | `sub(m, n)` with `import Grace.Cumulus.Nat.Subtraction` | keyboard symbol |
| `n % d` for naturals | `mod(n, d)` with `import Grace.Cumulus.Nat.Mod` | keyboard symbol |
| `x + y`, `x - y`, `x * y`, `-x` for rationals | `rationalAddValue(x, y)`, `rationalSubValue(x, y)`, `rationalMulValue(x, y)`, `rationalNegValue(x)` | keyboard symbols |
| `A + B`, `A - B`, `A * B`, `-A` for reals | `realAddValue(A, B)`, `realSubValue(A, B)`, `realMulValue(A, B)`, `realNegValue(A)` | keyboard symbols |
| `A ^ n` for a real and natural exponent | `realPow(A, n)` | keyboard symbol |
| `∫[A, B] f` | `riemannIntegral(f, A, B)` | `\int` followed by `[A, B] f` |
| `∑ k ≤ n, uₖ` | `realPartialSum(u, n + 1)`, the sum over `k < n + 1` | `\sum`, `\le` |
| `f′`, `f″`, `f′(x)` | `derivative(f)`, `derivative(derivative(f))`, `apply(derivative(f), x)` | `\prime`, `\dprime` |
| `f⁽ᵏ⁾`, `f⁽ⁿ⁺¹⁾(x)` | `iteratedDerivative(f, k)`, `apply(iteratedDerivative(f, n + 1), x)` | `\lsup`, `\supk`, `\supplus`, `\sup1`, `\rsup` |
| `n! * X`, `n < X` for a natural `n` and a real `X` | `realMulValue(realNat(n!), X)`, `relates(realLess, realNat(n), X)` | keyboard symbols |
| `∀ k ≤ n, φ`, `∃ k < n, φ` | `forall k, Nat(k) → k ≤ n → φ`, `exists k, Nat(k) ∧ k < n ∧ φ` | `\forall`, `\le` |
| `∀ X ⊆ V, φ`, `∃ X ⊆ V, φ` | `forall X, X ⊆ V → φ`, `exists X, X ⊆ V ∧ φ` | `\forall`, `\subseteq` |
| `∏ xs` for a list of naturals | `listProduct(xs)` | `\prod` |
| `√X` for a nonnegative real | `sqrt(X)` | `\sqrt` |
| `A < B`, `A ≤ B` for reals | `relates(realLess, A, B)`, `relates(realLe, A, B)` | keyboard symbols |

The finite-set forms are terms, including when they are the entire right-hand
side of a definition. Set comprehensions remain distinct because
they contain a top-level `|`, as in `{x ∈ A | P(x)}`.
The bounded integral is a value expression for an already defined real-valued
set function. Its laws require the relevant checked integrability hypotheses;
the raw `riemannIntegral(f, A, B)` spelling remains available.

## Bounded typed graphs

For a Nat or Real indexed expression whose result has either type, write:

```g17
defgraph dyadicRadii (n : Nat) : Real := dyadicRadius(n)
```

This defines the Replacement image `{ (n ↦ dyadicRadius(n)) | n ∈ ℕ }` and
checks four theorems: `dyadicRadii.closed` (the value has type Real),
`.relates`, `.function` (`FunctionBetween(dyadicRadii, ℕ, ℝ)`), and `.value`
(`dyadicRadii[n] = dyadicRadius(n)`). Nat and Real are supported for both
input and output; the corresponding carriers are `ℕ` and `ℝ`. If Grace17
cannot prove the value's declared type with `typecheck`, the declaration
fails at the codomain obligation. Graph existence uses bounded Replacement;
the generated functionality and value proofs replay in the kernel. For
arbitrary set domains and codomains, supply the closure proof yourself:

```g17
defgraph inclusionMap (A B : Set) (x ∈ A) : B := x
requires subset : A ⊆ B
proof
  unfold Subset at subset
  exact subset with x, member
```

This declares `inclusionMap(A, B).function` with the requirement `A ⊆ B`
and `inclusionMap(A, B).value` with that requirement and `x ∈ A`.
The graph is the bounded image `{ (x ↦ x) | x ∈ A }`. The proof block
establishes the codomain membership obligation; `member` names the
index's membership in its domain. Explicit Set, Nat, and Real parameters and
named `requires` clauses are supported, including multiline clauses. When
the domain is `ℕ` or `ℝ`, `.relates` and `.value` accept a Nat or Real index
directly; callers do not need to pass a separate membership proof. For
example, the Heine–Cantor witness graphs take
`(f S : Set, E : Real) (n ∈ ℕ) : ℝ` and a witness assumption. Their closure
proofs extract a real witness; their graph and application laws are generated.
The graph may have no additional parameters. For example:

```g17
defgraph identityOnOne (x ∈ {0}) : {0} := x
proof
  exact member
```

Its `.function` theorem has no term arguments, and its `.value` theorem takes
only the index and its membership proof. Named requirements are still allowed.

The indexed value may also be defined by Nat recursion. For example:

```g17
defgraph oneCellPoints (A B : Real) (n ∈ ℕ) : ℝ := oneCellPoint(A, B, n)
proof
  have point := oneCellPoint.real at A, B, n with *
  unfold Real at point
  exact point
```

The index is a Nat in the closure proof, so you prove only that the recursive
value is a real. The generated graph and function proofs are checked theorems.
The automatic form still supports single Nat and Real inputs and outputs
without a proof block.

## Checked bounded choice

Use `defchoose` to choose from a bounded predicate once an existence proof is
available:

```g17
defchoose failureFirst (f S : Set, E : Real, n : Nat) (X ∈ ℝ) :=
  ∃ Y ∈ ℝ, UniformFailurePair(f, S, E, dyadicRadius(n), X, Y)
requires witnesses : ∀ D ∈ ℝ, (0 < D →
  ∃ X ∈ ℝ, ∃ Y ∈ ℝ, UniformFailurePair(f, S, E, D, X, Y))
proof
  -- establish existence at dyadicRadius(n)
```

The proof block establishes `∃ X ∈ ℝ, ...`. Grace17 defines
`failureFirst.candidates` by bounded Separation, defines `failureFirst` as its
chosen member, and checks `.exists` and `.selected` as theorems. The selected
law states that the chosen value lies in `ℝ` and satisfies the predicate. The
selection property depends on the existence proof. Set, Nat, and Real
parameters and multiline requirements are supported. `rw under h at fact`
rewrites beneath a quantifier when the equality's source and replacement are
independent of its bound variable; plain `rw` keeps its usual scope.

## Expression carrier annotations

Use `(0:R)` to select the real zero when an unannotated numeral is ambiguous.
`R`, `N`, `Z`, and `Q` abbreviate `Real`, `Nat`, `Integer`, and `Rational`;
their full names and `ℝ`, `ℕ`, `ℤ`, `ℚ` work too. On a non-numeral, such as
`(p[i]:R)`, the annotation selects overloaded notation: `(p[i]:R) <
(p[succ(i)]:R)` uses real order. The annotation is an elaboration hint and
assumes no membership; operations still need carrier evidence in the proofs
that use them. An unavailable typed numeral or a known conflicting type is
rejected.

The annotation also reaches a prefix or infix notation inside the
parentheses: `(-1:Z)` is the integer negation of the integer one, and
`(x - 1 : R)` reads the real difference. A numeral under an overloaded
prefix or infix is usually resolved without one, by the sort of the position
it sits in: the parameter it fills in a function or predicate application,
so that `integerPow(-1, k)` reads `-1` as an integer whatever other negations
are visible, or the sort of the other operand of an infix, so that `X * -1`
with `X` real reads a real. Only a numeral whose position fixes no sort, such
as `-1 = -1` on its own with the integers, rationals, and reals all visible,
is rejected, with the candidate sorts and the annotations that select them.

A comparison whose operands carry no sort of their own, two values of a
`Set`-valued function under `(p q : Rational)` binders, is read in the sort
the function's typing theorem gives its values: `rationalCut(p) <
rationalCut(q)` is the real order, by `rationalCut.real`, and `rationalCut(p)
< 0` reads the real zero. A function whose values are typed in several
carriers is rejected on such a comparison, with the candidates and the
annotation that selects each, `(twice(a):Q)` or `(twice(a):R)`. Operands
with no such function on either side keep the natural order, the library's
default.

## Seeing the elaboration

Hover the parentheses or comma of an ordered pair, or either brace of a finite
set literal, in the Workbench to see its desugaring and the definition of
`empty`, `singleton`, `pair`, or `union2`. Hover `∈`, `↦`, `⋃`, `𝒫`, `∪`,
`∩`, `∖`, `×`, `⧸`, `⊆`, `⊂`, a number-carrier glyph, the brackets of
`⟦x⟧[A, r]`, or another declared notation to see its target symbol and
elaboration;
Command-click or Control-click follows that target to its definition. Goals
and theorem statements use mathematical notation by default, while exported
proof certificates retain canonical symbol names.

Subscripts are postfix application syntax. A representable Unicode
suffix such as `uₙ` or `a₁₂` elaborates to `apply(u, n)` or
`apply(a, 12)`. Bracket form accepts any index term, as in `u[n + 1]`.
Two indices use the ordered pair as a single argument: `M[i, j]` elaborates
to `apply(M, (i, j))`. This is the preferred entry syntax for a
`RealMatrix(M)`; `M[(i, j)]` is equivalent. The Workbench hover on `M[i, j]`
shows the ordered-pair application. An already declared name wins, so a
constant such as `ε₀` stays a constant.

The names remain available everywhere the notation is available. This is
useful when unfolding or naming facts:

```g17
theorem notation_and_raw (x y : Set)
  requires h : x in singleton(y)
  shows x ∈ {y}
proof
  exact h
```

Tactics also accept a visible notation token wherever they accept its
underlying definition. For example, `unfold %` and `unfold mod` are identical
when remainder notation is in scope.

Arithmetic notation may be overloaded by checked soft type:

```g17 fragment
notation infixl 60 "+" => add for Nat
notation infixl 60 "+" => rationalAddValue for Rational
notation prefix 75 "-" => rationalNegValue for Rational
```

Thus `m + n` selects `add` when `m` and `n` are natural, while `x + y`
selects `rationalAddValue` when they are rational. Here `for Rational` names a
unary predicate used as a soft type. It has nothing to do with type-class
instances or with the `class` declaration form. Operand evidence may come from a
typed binder, a named requirement, or a checked local fact introduced by a
proof step such as `obtain`. If the evidence does not determine one visible
implementation, elaboration reports the predicate and target alternatives.
`unfold +` uses the operation occurring in the selected goal or local fact; the
raw names remain available as an escape hatch.

Infix operations may also have different left and right operand types. The
two predicates are written in operand order:

```g17 fragment
notation infixr 80 "^" => realPow for Real, Nat
```

This declares the heterogeneous signature `Real × Nat → Real`, so
`A ^ n` selects `realPow` while `m ^ n` continues to select natural `pow`.
Hover shows the selected signature and jumps to the corresponding definition.

Prefix notation uses the same typed, import-scoped resolution and precedence
rules as infix notation. It is elaborator metadata: the rational `-x` becomes
`rationalNeg(x)`, the application of the negation graph, whose graph and laws
are checked by the kernel.

For algebraic notation, the preferred form obtains the implementation from a
proof-producing type-class instance:

```g17 fragment
instance rationalAdd.operation
  shows AddOperation(ℚ, rationalAdd)
proof
  unfold AddOperation
  exact rationalAdd.function

notation infixl 60 "+" => call2 via AddOperation(ℚ, _) for Rational
notation numeral "0" via OfNat(ℚ, 0, _) for Rational
```

The `for Rational` clause still supplies only the operand soft type. The
separate query `AddOperation(ℚ, _)` asks the import-scoped instance registry to
produce its output operation. Exactly one checked instance must succeed. The
result above elaborates `x + y` to `call2(rationalAdd, x, y)`; the `_` is never
present in the kernel term. Numerals are expected-type directed, so `A + 0`
uses the `OfNat` instance selected for the same operand type, while an
unconstrained `0` keeps its natural-number interpretation.

Numeral instance outputs may be closed compound expressions as well as named
constants. A numeral template covers every literal at once: Cumulus declares

```g17 fragment
notation numeral _ => realNumeral(_) for Real
```

so `(7:R)`, or a bare `7` where a real is expected, is `realNumeral(7)`, a
function of its own so that rewriting `0`, `1`, or `realNat` never reaches
inside a numeral. The theorem `realNumeral.numeral` identifies it with
`ringNat(realAdd, realZero, realOne, 7)`, the seven-fold sum of one from
`Algebra.Ring.Numeral`, and `ring` uses that bridge to read the numeral as
the coefficient 7; `linarith` reads it as seven ones. A specific declaration
such as the one for `1` takes precedence over the template for its literal,
and goals display every numeral term as the numeral again. Any type can
declare a template the same way, with a `<function>.numeral` bridge when its
ring should understand the coefficients. A scoped ring without a template,
such as ℂ, spells `3` as `ringNat(complexAdd, complexZero, complexOne, 3)`
directly; `complexNumeral.pair` identifies it with the pair `(3, 0)`.

### Big operators

A binder notation writes a sum over an index below a bound the way it is
written on paper. Cumulus declares, next to `realPartialSum`,

```g17 fragment
notation binder "∑" => realPartialSum for Real
```

after which `∑ k < n, uₖ` (or `∑ k < n, u(k)`) is `realPartialSum(u, n)`,
and goals and statements print the sum in that form again. An inclusive
bound, `∑ k ≤ n, uₖ`, is the sum over `k < n + 1`, `realPartialSum(u, n + 1)`,
and a sum whose bound is written `n + 1` prints inclusively. The index is a
natural number in the body, so `k!` and `(B - A) ^ k` read as they would
under `(k : Nat)`. The body extends over a product and stops at a sum, as
on paper: `∑ k ≤ n, uₖ * vₖ + w` is the sum plus `w`, a sum used as a
factor is parenthesized, as in `6 * (∑ k < n, squareTerms(k))`, and a sum
that is a summand prints without parentheses. The body must apply a
sequence to the bound variable; the sequence may be any term not
mentioning it, such as `arithmeticTerms(A, D)`, so
`∑ k < n, arithmeticTerms(A, D)(k)` is the sum of the first `n` terms of an
arithmetic progression. The target of a binder notation is any function of
two arguments, the sequence and the bound.

A sequence defined as a bounded graph may be written out by its value.
Cumulus declares, after `defgraph taylorTerms (f : Set, X B : Real) (k ∈ ℕ) : ℝ
:= iteratedDerivative(f, k)(X) * (B - X) ^ k / k!`,

```g17 fragment
notation sequence taylorTerms
```

after which a body that is the value of the graph at the bound variable,
with the parameters as pattern variables, is the sum of that sequence:
`∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k!` is `∑ k ≤ n, taylorTerms(f, A, B)(k)`,
the term `realPartialSum(taylorTerms(f, A, B), n + 1)`, and a sum of such a
graph prints with the value written out. The value is read off the graph's
membership law, so nothing is declared twice; a body that is neither an
application of a sequence nor the value of a declared one is an error that
says so.

### Postfix operators and aliases

`notation postfix 90 "!" => factorial for Nat` makes `n!` the factorial,
binding tighter than `*`, so `(n + 1)! = (n + 1) * n!` reads as in a textbook.
A postfix token may be a modifier letter: `notation postfix 90 "ᵀ" =>
transpose` makes `Mᵀ` the transpose, the letter ending the name before it.
A postfix form may be applied to arguments like any term: Cumulus declares
`notation postfix 95 "′" => derivative`, so `f′` is `derivative(f)` and
`f′(x)` its value `derivative(f)(x)`; a doubled or tripled prime is that many
primes, `f″` being `derivative(derivative(f))`, and the forms print back as
`f′(x)` and `f″`. A postfix token may carry an index between two halves,
written `_` in the declaration: `notation postfix 95 "⁽_⁾" => iteratedDerivative`
takes a function of two arguments, the operand and the index, and `f⁽ᵏ⁾`
is `iteratedDerivative(f, k)`. The index is written in superscript digits,
letters, and signs, so `f⁽ⁿ⁺¹⁾(C)` is `iteratedDerivative(f, n + 1)(C)`,
and an index with no superscript spelling, such as `succ(j)`, prints by the
function's name. A prime after an indexed form needs no parentheses, `f⁽ᵏ⁾′`,
and `f⁽ᵏ⁾ : ℝ → ℝ` is a mixfix predicate on the form.
An infix operator may be a word: `notation infixl 55 "choose" => choose for
Nat` makes `n choose k` the binomial coefficient, read only between two
operands so it never shadows the function's own name, and at precedence 55
the operands extend past `+`, so `2 * n + 1 choose k` is the coefficient of
`2n + 1`; printing parenthesizes it inside a product and brackets an operand
that is a sum, `(2 * n + 1) choose k`, whatever the precedences allow.
`notation alias "D" => f` lets a function be written and printed under another name, `D(x)`,
without introducing a new symbol or an unfolding step; a variable of the
same name in scope still denotes the variable.

### Coercions

A sort may be read into another where the position asks for it. Cumulus
declares, next to `realNat`,

```g17 fragment
notation coercion realNat for Nat, Real
```

after which a natural number in a real position is `realNat` of it: an
operand of a real `+`, `-`, `*`, or `/` whose other operand is real, an
operand of a real comparison, or one side of an equation whose other side
is real, so `n! * X`, `n < X`, and `k! = X` are `realNat(n!) * X`,
`realNat(n) < X`, and `realNat(k!) = X` under `(n k : Nat) (X : Real)`.
A term is coerced when its own sort is known, by a binder, a numeral
notation such as `n!`, a natural operation such as `n + 1`, or the index of
a big operator; a numeral keeps its typed declarations, so `2 * X` is still
`realNumeral(2) * X`, and nothing changes outside a real position, so `n + 1`
beside a natural stays natural. The explicit `realNat(n)` remains available
and elaborates to the same term. Statements and goals print a coerced term
without the coercion wherever its neighbour shows the sort, `n! * X` under
`∀ X : ℝ` and `(n + 1)! = f(B)` under `(f : ℝ → ℝ)`, and keep `realNat(n)`
beside a numeral or a term of unknown sort, where the text would otherwise
read back as a natural operation.

### Mixfix predicates

`notation mixfix "_ : _ → _" => FunctionBetween` writes a predicate with its
arguments in the placeholders around literal tokens: `f : A → B` is
`FunctionBetween(f, A, B)`, and `->` is accepted for `→`. The pattern begins
and ends with a placeholder, placeholders alternate with punctuation tokens,
and the target takes as many arguments as there are placeholders. The form
is read only when every placeholder holds a term, so `n : ℕ → n ∈ S` is still
an implication. On its own line a statement or goal prints in this form;
inside a larger formula the predicate keeps its spelling, as a sort
ascription does.

A mixfix notation that starts with the colon also types a binder:
`theorem value (A B : Set) (f : A → B) (x : Set)` makes `f` a set variable
guarded by `FunctionBetween(f, A, B)`, exactly as `(n : Nat)` guards `n` with
`Nat(n)`. The guard is a generated requirement, so `with *` discharges it from
a hypothesis in scope or by instance synthesis: `compose.function`,
`identity.function`, `constantFunction.function`, and
`pairFunctions.function` are instances, so a guard `compose(g, f, A, B, C) : A → C`
follows from `(f : A → B)` and `(g : B → C)` without being named. The guard
comes first among the requirements when the theorem is applied with a
positional `with` list. A value `f(x)` of such a function carries the sort
of the codomain for the notation around it and for the typing rules: under
`(f : ℝ → ℝ)` the equation `f(B) = 0` reads the real zero and `f(B) - f(A)`
the real difference, with no `(f(B):R)` annotation; the annotation is still
accepted. The statement prints the binder back as written, `∀ (f : ℝ → ℝ),
∀ A B : ℝ, …`, and the same holds for any `:`-pattern that guards a
variable after the quantifier prefix.

### Hom-typed binders

A predicate supplied by a hypothesis may also be written as a mixfix form
whose fixed arguments come from the hypothesis. Cumulus bundles a small
category as one set `C`, the [structure](datatypes.md#structures)
`Category` with projections `C.obj`, `C.mor`, `C.dom`, `C.cod`, `C.id`, and
`C.comp`, and declares, next to it,

```g17 fragment
predicate Morphism (C f a b : Set) :=
  f ∈ C.mor ∧ C.dom(f) = a ∧ C.cod(f) = b

notation mixfix "_ : _ ⟶ _" => Morphism(C, _, _, _) via hypothesis Category(C) for C.obj, C.mor
```

The target names the predicate with `_` at the placeholders of the pattern
and terms over the pattern variables of the hypothesis at the other
positions; `for C.obj, C.mor` names the objects and the morphisms.
Wherever a `Category(C)` is in scope, the binder `(f : a ⟶ b)` makes `f` a
set variable guarded by `Morphism(C, f, a, b)`, the formula `f : a ⟶ b` is
that predicate, and statements, assumptions, and locals print it back as
`f : a ⟶ b`, parenthesized inside a larger formula. The same binders are
accepted under a quantifier: `∀ (a b ∈ obj(C)) (f : a ⟶ b), φ` quantifies
over `a`, `b`, and `f` with each guard in scope for the later binders and the
body, and prints back in that form; a bounded quantifier `∀ a b ∈ X, φ`
binds several variables at once. A functor hypothesis `F : C ⥤ D` supplies
the shape for both of its categories, and the operands choose between them
as they do for `∘`: an endpoint that is a member of the objects, a morphism
that is a member of the morphisms or of a hom-set, a value of a function
into them, or a morphism already typed in one of them. The binder
`(a b ∈ obj(C))` guards set variables by membership and supplies that
evidence, so under a functor `(a b c ∈ obj(C)) (f : a ⟶ b) (g : b ⟶ c)`
types the morphisms in the source and `F(f) : F(a) ⟶ F(b)` in the target;
under one category alone no object binder is needed, since `a ∈ obj(C)`
follows from the guard of `f`. With two categories and no evidence the form
is an error that asks for an object binder; with no supplying hypothesis it
names the shapes it accepts. The `for` clause may be omitted when the
hypothesis has no carrier for that shape.

The predicate of such a declaration is a transparent guard: a local fact
`f : a ⟶ b` is opened to `f ∈ C.mor`, `C.dom(f) = a`, and `C.cod(f) = b`
wherever local evidence is consulted, so `with *`, `assumption`,
`typecheck`, `cc`, and the side conditions of `simp` and `rw` see the three
facts, and an equation between endpoints such as `dom(C)(g) = cod(C)(f)`
follows by congruence closure. A plain mixfix declaration written
`notation guard "_ : _ ⥤ _" => Functor` makes its predicate a transparent
guard too: `F : C ⥤ D` opens to the shape of `F`, the categories, the two
maps, the functor laws, and the source and target of `F`. Instances synthesize the guards of composites, identities, and
images: `Morphism.comp` gives `g ∘ f : a ⟶ c` from `(f : a ⟶ b)` and
`(g : b ⟶ c)`, `Morphism.id` gives `id(C)(a) : a ⟶ a` from `a ∈ obj(C)`,
`Functor.map_hom` gives `F(f) : F(a) ⟶ F(b)`, and
`NaturalTransformation.component_hom` gives `η(a) : F(a) ⟶ G(a)`. An
instance or a theorem used as a rule may leave a variable out of its
conclusion when a premise of a hypothesis shape or guard fixes it, as the
middle object `b` is fixed by the guards of the factors; such a premise is
matched against the local facts, and a guard with an open endpoint and no
local fact of its shape is completed through the rules and instances,
trying each completion in turn, so `Category.id_right with *` applies to
`(g ∘ f) ∘ id(C)(a)` without naming `c`, and `Functor.map_comp` rewrites
`G(F(g) ∘ F(f))` with the images typed by `Functor.map_hom`. A membership
premise of an instance that no instance proves, such as `F(a) ∈ obj(D)`, is
left to the certified type rules. A `simp` on a guard goal rewrites it to a
fixpoint and then closes it by the search or the instance registry.

The laws are stated on hom binders: `Category.id_left (f : a ⟶ b)`,
`Category.id_right`, `Category.assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)`,
`Functor.map_id`, `Functor.map_comp`, `Functor.map_hom`,
`NaturalTransformation.component_hom`, and
`NaturalTransformation.naturality (f : a ⟶ b)`. As `simp` and `rw` rules
they rewrite where the guards of the morphisms involved are in scope;
`category_simp` and `functor_simp` name the two sets. A proof reads

```g17 fragment
theorem InversePair.unique (a b : Set) (f : a ⟶ b) (g k : b ⟶ a)
  requires gf : g ∘ f = id(C)(a)
  requires fk : f ∘ k = id(C)(b)
  shows g = k
proof
  calc
    g = g ∘ id(C)(b) := by simp [Category.id_right]
    _ = g ∘ (f ∘ k) := by rw fk
    _ = (g ∘ f) ∘ k := by rw Category.assoc
    _ = id(C)(a) ∘ k := by rw gf
    _ = k := by simp [Category.id_left]
```

with the category coming from the section hypothesis `category : Category(C)`.

### Functors applied

A functor is the structure `Functor (C D : Set)` of its object map, its
morphism map, and its source and target, read back by `F.obj`, `F.map`,
`F.src`, and `F.tgt`; the predicate `Functor(F, C, D)` is written
`F : C ⥤ D`. Wherever such a fact is in scope, `F(x)` is `F.obj(x)` when
the local facts place `x` among the objects of `C` and `F.map(x)` when they
place it among the morphisms: by a membership `x ∈ C.obj` or `x ∈ C.mor`, a
hom-set membership, a guard `(f : a ⟶ b)` or an endpoint of one, the
definitional conjuncts of a fact such as `InversePair(C, f, g)`, a composite
`g ∘ f`, or a value `C.id(a)`, `C.dom(f)`, `G(x)` of a function into one of
the two sets. An argument the facts do not place is an error that names
both spellings. Statements and goals print `F.obj(x)` and `F.map(x)` as
`F(x)` while a functor or transformation hypothesis about `F` is in scope,
so the functor laws read `F(g ∘ f) = F(g) ∘ F(f)` and
`F(C.id(a)) = D.id(F(a))`. The categories of
`Sets(U)`, whose morphisms apply as functions, let `F(f)(x)` be written for
a functor `F : C ⥤ Sets(U)`, and `F(g ∘ f)(x) = F(g)(F(f)(x))` follows from
`Functor.map_comp` and `Sets.comp_apply` in one `simp`.

### Operations supplied by a hypothesis

An algebraic structure often arrives as a hypothesis rather than as a
registered instance: a theorem about an arbitrary category carries
`Category(C)`, and its composition `C.comp` is a projection of the
parameter. `via hypothesis` binds a token to a term over such a parameter at
each use:

```g17 fragment
notation infixr 70 "∘" => call2(C.comp, _, _) via hypothesis Category(C) for C.mor
```

The target applies the binary application symbol to the operation, a term
over the pattern variables of the hypothesis, and the two operand
placeholders; `for C.mor` names the carrier. The templates are read under
the hypothesis itself, so a projection such as `C.obj` under
`Functor(F, C, D)` finds the category that the guard opens to. Wherever a hypothesis in scope
matches the shape, whether a section hypothesis, an earlier `requires`, an
earlier conjunct or antecedent of the same formula, or a fact in the proof
state, `g ∘ f` is `C.comp(g, f)`, and goals and locals print it back the
same way. The same token may be declared for several shapes: `Functor(F, C,
D)` supplies the compositions of both its categories, `InversePair(C, f, g)`,
`Monomorphism(C, f)`, and the others supply theirs, and when more than one
operation is available the operands decide, by membership in a carrier, by
lying in a hom-set, by being the value of a function into the carrier, or,
for the component `η(a)` of a transformation `η : F ⟹ G`, by the target of
`F`. With no matching hypothesis the token is an error that names the shapes
it accepts, and when two operations share a carrier and the operands do not
separate them, the error asks for the operation by name. Nothing reaches the
kernel but the application `C.comp(g, f)`. The requirements of a `defgraph`
and the membership of its index are in scope for its value, so a graph may
be defined by `g ∘ f` under a `Category(C)` requirement.

### Functions supplied by a hypothesis

A function may be written with an identifier and still take its remaining
arguments from a hypothesis in scope. Cumulus declares, next to the
kernel of a ring homomorphism,

```g17 fragment
notation function "ker(f)" => ringKernel(f, R, S[0]) via hypothesis RingHom(f, R, S)
```

The parameters in the token are the written arguments, and the target is a
term over them and the pattern variables of the hypothesis, which supplies
the rest. A parameter named as a pattern variable is that argument of the
hypothesis: `ker(f)` is read off the hypothesis about `f`, so under
`f : R →+* S` it is `ringKernel(f, R.carrier, S.zero)`, under `f : G →* H`
the same spelling is the group kernel `kernel(f, G, H)`, and with two
homomorphisms in scope `ker(f)` and `ker(g)` are each read off their own.
A parameter that is not a pattern variable is a free placeholder:
`notation function "d(x, y)" => X.dist(x, y) via hypothesis MetricSpace(X)
for X.carrier` makes `d(x, y)` the distance of whichever space in scope the
arguments lie in, the carrier named by `for` deciding between several as
the operands of an infix form do, and the error asks for the function by
name when they do not. A template may use a form declared earlier, so the
map a homomorphism induces on the quotient by its kernel is

```g17 fragment
notation function "inducedMap(f)" => quotientMap(f, R.carrier, S.carrier, quotientRelation(R, ker(f))) via hypothesis RingHom(f, R, S)
```

and the first isomorphism theorem reads `inducedMap(f) : R ⧸ ker(f) ≃+* S`.
A local variable of the name is applied as a function as always, and a
declared function of the name is read when no hypothesis in scope supplies
the form at that arity, so `kernel(f, G, H)` and `ringKernel(f, A, z)`
remain available by name; with a supplying hypothesis the form wins, and
with none and no such function the error names the shapes it accepts.
Statements and goals print a term matching the template back as the form,
`ker(f)`, `inducedMap(f)`, and `d(x, y)`, wherever a supplying hypothesis
is in scope; when two hypotheses would print different terms the same way
and no carrier tells their arguments apart, the terms print by name.

### Groups: carrier binders and unary operations

Cumulus bundles a group as the structure `Group` with the fields `carrier`,
`mul`, `one`, and `inv`, read back as `G.carrier`, `G.mul`, `G.one`, and
`G.inv`, and declares, next to the generated predicate `Group(G)`,

```g17 fragment
notation infixl 70 "*" => call2(G.mul, _, _) via hypothesis Group(G) for G.carrier
notation postfix 90 "⁻¹" => apply(G.inv, _) via hypothesis Group(G) for G.carrier
notation infixr 80 "^" => groupPow(G, _, _) via hypothesis Group(G) for G.carrier
```

A unary `via hypothesis` notation is declared with `prefix` or `postfix`,
and its target applies the projected operation to one placeholder: `a⁻¹`
is `G.inv(a)` wherever a `Group(G)` is in scope, and goals print it back
with the token, `(a * b)⁻¹` parenthesizing an operand that binds more
loosely. The same tokens are declared for `Monoid(G)` and `AbelianGroup(G)`,
for `Subgroup(H, G)` with the carrier `H`, and for `NormalSubgroup(N, G)`,
so a subgroup hypothesis alone supplies the operation on its elements. An
operation declared under a hypothesis coexists with the typed declarations
of the same token, and the operands decide between them. An operand placed
in the carrier of a supplying hypothesis, by a binder, a membership fact,
being a composite already read under the hypothesis, or the certified
typing rules, keeps the hypothesis: `a * b` and `a ^ 2` are the group
operations, and so is `G.one ^ 1`, because `Group.one_mem` places the unit
in `G.carrier`. With no operand so placed, an operand whose sort names a
typed declaration, by its syntax, a local fact, or the typing rules,
selects it, so `n * m`, `2 ^ n`, and `index(G, H) * cardinality(H)` stay
natural arithmetic inside a group section once one operand is known to be
a natural number; an operand with neither selects the hypothesis, and with
no supplying hypothesis in scope the token falls back to its typed
declarations. When two groups are in scope and no operand is placed
syntactically, the typing rules decide: `G.one * G.one` is the operation of
`G`.

A binder may be typed by the structure itself: `(a b : G)` under a
hypothesis `Group(G)` makes `a` and `b` set variables guarded by
`a ∈ G.carrier` and `b ∈ G.carrier`, the carrier named by the
hypothesis notation of `Group`, and `(h : H)` under `Subgroup(H, G)` is
`h ∈ H`. The structure must be a variable in scope and the carrier a term of
that variable alone, so under `Subgroup(H, G)` the binder `(a : G)` is not
read as membership in `H`; when two hypotheses give one variable different
carriers the binder is an error that asks for a membership binder. The
hypothesis may come later in the same header: `theorem t (G : Set) (g h : G)`
followed by `requires group : Group(G)` resolves the binders once the
requirements are read, and a binder with no supplying hypothesis is an error
that says so. `(1 : G)` under the hypothesis is the unit `G.one`, and
`(0 : R)` and `(1 : R)` the zero and one of a ring `R`; a bare `1` beside a
group operation stays the natural number. The
guard is a membership, so `with *`, `assumption`, `typecheck`, `cc`, and the
side conditions of `simp` and `rw` see it, and statements and goals print
it back as the carrier binder, `∀ (a b : G), Group(G) → …`, wherever a
hypothesis in scope gives `G` that carrier. The closure
instances `Group.mul_mem`, `Group.one_mem`, `Group.inv_mem`, and
`Group.pow_mem` synthesize the carrier membership of a compound term, and
`Subgroup.mul_mem`, `Subgroup.one_mem`, `Subgroup.inv_mem`, and
`Subgroup.pow_mem` its subgroup membership; `Subgroup.mem_carrier` is the
typing rule from `h ∈ H` to `h ∈ G.carrier`. Where a set of elements is
meant, the structure variable names its carrier: under `Group(G)` the
container of `x ∈ G` and `∀ x ∈ G`, the operands of `S ⊆ G`, and the
arguments of `cardinality(G)` and `Finite(G)` are read at `G.carrier`, and
statements and goals print them back as written; a variable that no
hypothesis in scope gives a carrier, or that two give different carriers,
is left as it is, and every other position, `order(G)` or `Group(G)`,
takes the structure itself. The same holds for `R` under `Ring(R)` and for
`P` under an order hypothesis. A rule variable that the
conclusion leaves open is bound by a hypothesis-shaped premise wherever it
stands among the premises, so `Subgroup(H, G)` binds `H` for a rule whose
premise `h ∈ H` comes earlier.

The left coset `leftCoset(G, g, H)` is `g • H` under either `Group(G)` or
`Subgroup(H, G)`, declared with the three-place function as the target and
the group as the operation,

```g17 fragment
notation infixr 73 "•" => leftCoset(G, _, _) via hypothesis Group(G) for G.carrier
```

so both operands are written, `g • H = H ↔ g ∈ H` is `leftCoset.eq_self_iff`,
and a statement under a group hypothesis prints its cosets the same way.

The quotient of a group by a normal subgroup is `G ⧸ N`, the value
`quotientGroup(G, N)`, declared with the structure itself as the left
operand:

```g17 fragment
notation infixl 70 "⧸" => quotientGroup(G, _) via hypothesis Group(G) for G
```

A target `f(G, _)` with one placeholder, and `for G` naming the structure
rather than a carrier, declares an infix form whose left operand is the
structure. The form is read when the left operand is a variable or constant
that a hypothesis in scope makes a structure of the declared kind, whether a
section hypothesis, an earlier `requires`, a binder `(G : Group)`, a fact in
the proof state, or a closed instance such as `CommRing(integerRing)`, and
the right operand is written as it stands; on any other left operand the
token falls back to its other declarations, so `G.carrier ⧸ cosetRelation(G, N)`
and `A ⧸ r` on a plain set are the set quotient `quotient(A, r)` under the
same hypotheses. Such a form shadows none of the declarations it falls back
to, in the module that declares it as elsewhere, and names no carrier, so a
binder `(a : G)` is unaffected by it. The same token is declared for
`NormalSubgroup(N, G)`, and statements and goals print `quotientGroup(G, N)`
back as `G ⧸ N` wherever a hypothesis in scope gives `G` the structure; the
carrier of the quotient is `Group.carrier(G ⧸ N)`, the set quotient
`G.carrier ⧸ cosetRelation(G, N)`. When two forms with different targets
claim one structure, the error asks for the function by name. The
order of a group is `order(G)` and the index of a subgroup `index(G, H)`;
Lagrange's theorem reads `order(G) = index(G, H) * cardinality(H)`, the
natural product, because the instance `index.nat` places the index in `ℕ`
and neither operand lies in the group.

Homomorphisms are the guard `notation guard "_ : _ →* _" => GroupHom`: a
hypothesis `f : G →* H` opens to `Group(G)`, `Group(H)`, the function
`f : G.carrier → H.carrier`, and the law, so it supplies both
operations, and `f(a * b) = f(a) * f(b)` resolves the first `*` in `G` by
the operands' membership and the second in `H` by the codomain of `f`.
`f : G ≃* H` is a bijective homomorphism and `G ≃* H` says one exists.
The kernel is `ker(f)`, the set `kernel(f, G, H)`, and the map `f` induces
on the quotient by its kernel is `inducedMap(f)`, both [functions supplied
by the hypothesis](#functions-supplied-by-a-hypothesis), so the first
isomorphism theorem reads `inducedMap(f) : G ⧸ ker(f) ≃* H`.

The laws have short standard names such as `mul_assoc`, `one_mul`, and
`inv_inv`, each stated on carrier binders, and `group_simp` names the
rewrite set. A proof reads

```g17 fragment
theorem inv_mul_cancel_left (a b : G)
  shows a⁻¹ * (a * b) = b
proof
  rw [← mul_assoc, Group.inv_mul, one_mul]
  rfl
```

with the group coming from the section hypothesis `group : Group(G)`.

### Rings supplied by a hypothesis

Cumulus bundles a ring as the structure `Ring` with the fields `carrier`,
`add`, `zero`, `neg`, `mul`, and `one`, and declares, next to the generated
predicate `Ring(R)` and the predicates `CommRing(R)`, `Field(R)`, and
`OrderedField(R, lt)` over it,

```g17 fragment
notation infixl 60 "+" => call2(R.add, _, _) via hypothesis CommRing(R) for R.carrier
notation infixl 70 "*" => call2(R.mul, _, _) via hypothesis CommRing(R) for R.carrier
notation prefix 75 "-" => apply(R.neg, _) via hypothesis CommRing(R) for R.carrier
```

so that under such a hypothesis `x + y` is `R.add(x, y)`, `-x` is
`R.neg(x)`, a binder `(x : R)` is `x ∈ R.carrier`, and the typed `+` of `ℕ`,
`ℤ`, `ℚ`, and `ℝ` keeps its meaning on operands of those sorts.
Subtraction is the addition of the negation, `Ring.sub(R, x, y)`, declared

```g17 fragment
notation infixl 60 "-" => Ring.sub(R, _, _) via hypothesis Ring(R) for R.carrier
```

so that `x - y` is read under the same hypotheses and prints back the same
way; `Ring.sub.value` unfolds it to `x + (-y)`, the form the ring tactics
read, and `Ring.sub_mem` keeps it in the carrier. A prefix
operation declared under a hypothesis is read exactly as a postfix one. The
constants and numerals of the ring are written `R[0]`, `R[1]`, `R[2]`: the
name of a ring structure before `[`, a variable under a hypothesis or a
constant such as `integerRing` under a closed instance `CommRing(integerRing)`,
opens the [ring scope](algebra.md#rings) of its
projections for the bracketed term, and goals print
`ringNat(R.add, R.zero, R.one, 2)` back as `R[2]`. A closed instance also
supplies the infix tokens where no hypothesis does, so `x + y` on members of
`integerRing.carrier` is the addition of that ring. A constant may be the
receiver of a projection, `integerRing.carrier`, and prints that way.

A structure built by a constructor, or by a definition whose body is one,
is supplied by an instance whose premises hold in scope: under `CommRing(R)`
the instance `polynomialRing.comm_ring` gives `CommRing(polynomialRing(R, I))`,
so the binder `(p : polynomialRing(R, I))` is `p ∈ Ring.carrier(polynomialRing(R, I))`,
the membership `p ∈ polynomialRing(R, I)` and the subset `G ⊆ polynomialRing(R, I)`
are read at that carrier, `p + q`, `p * q`, and `p - q` on its elements are
its operations, and `polynomialRing(R, I)[2]` is its numeral, with no
hypothesis naming the instance. An element is placed in such a structure
by a binder or a membership fact, or by the certified typing rules when
the facts place it nowhere, as the instance `X.mem` places `X(R, I, j)` in
the polynomial ring; the search is the bounded instance search of `with *`
under the facts in scope, tried only for terms built by a structure's
constructor, and statements and goals print the binders and memberships
back as written.

The ideal theory uses the same notation. `Ideal(R, I)`, `ProperIdeal(R, I)`,
`MaximalIdeal(R, M)`, `PrimeIdeal(R, I)`, and `Subring(R, S)` take the ring
first, and each supplies the operations on its own elements: under
`Ideal(R, I)` a binder `(x : I)` is `x ∈ I`, and `x + y`, `x * y`, `-x`, and
`x - y` are the operations of `R`, declared as
`notation infixl 60 "+" => call2(R.add, _, _) via hypothesis Ideal(R, I) for I`.
A ring homomorphism is the guard `notation guard "_ : _ →+* _" => RingHom`,
so a hypothesis `f : R →+* S` opens to `Ring(R)`, `Ring(S)`, and
`f : R.carrier → S.carrier` and supplies both rings, the second `+` of
`f(x + y) = f(x) + f(y)` resolving in `S` by the codomain of `f`;
`f : R ≃+* S` is a bijective homomorphism. The kernel of `f` is `ker(f)`,
a [function supplied by the hypothesis](#functions-supplied-by-a-hypothesis)
that stands for the set `ringKernel(f, R.carrier, S.zero)`. The functions
`ringKernel`, `idealComap`, and `idealMap` take sets of elements, so, as
for `cardinality(G)`, a structure variable in their arguments is read as
its carrier and printed back: `ringKernel(f, R, S[0])` is
`ringKernel(f, R.carrier, S.zero)`. The quotient by an ideal is the ring
value `quotientRing(R, I)`, written `R ⧸ I` under `Ring(R)`, `CommRing(R)`,
or `Ideal(R, I)` exactly as the [quotient
group](#groups-carrier-binders-and-unary-operations) is written `G ⧸ N`,
with the structure as the left operand and the set quotient on every other
one; its carrier is `R.carrier ⧸ quotientRelation(R, I)` and its classes are
written `⟦x⟧[R.carrier, quotientRelation(R, I)]`. The first isomorphism
theorem reads `inducedMap(f) : R ⧸ ker(f) ≃+* S`, the induced map being
the descent of `f` to the quotient by its kernel.

### Orders supplied by a hypothesis

Cumulus bundles an ordered set as one set `P`, the structure `Order` with
projections `P.points` and `P.le`, built by `Order.mk(A, r)`, and states
every order structure as a property of `P`: `Preorder(P)`, `PartialOrder(P)`,
`LinearOrder(P)`, `Lattice(P)`, `BoundedLattice(P)`, `CompleteLattice(P)`,
`DistributiveLattice(P)`, `BooleanAlgebra(P)`. The order is a predicate
`Le(P, a, b) := relates(le(P), a, b)` of its own, declared as an infix
predicate read off the hypothesis:

```g17 fragment
notation infix 50 "≤" => Le(P, _, _) via hypothesis PartialOrder(P) for P.points
notation infixl 68 "⊔" => call2(sup(P), _, _) via hypothesis Lattice(P) for P.points
notation infixl 69 "⊓" => call2(inf(P), _, _) via hypothesis Lattice(P) for P.points
```

A `via hypothesis` target may be a predicate as well as an operation: its
fixed arguments are templates over the pattern variables, and its two
placeholders are the operands. Wherever a hypothesis of one of the declared
shapes is in scope, `a ≤ b` is `Le(P, a, b)`, `a ⊔ b` is the join
`sup(P)(a, b)`, and `a ⊓ b` the meet. The token `≤` is also the typed order
of `ℕ`, `ℤ`, `ℚ`, and `ℝ`, and the operands decide between the two: the
hypothesis form is read when an operand lies in `P.points`, by a membership
binder or fact, by being a join, a meet, or another composite read under
the hypothesis, by being the value of a function into the points, or by the
certified typing rules, and no operand outside the points carries one of
the typed sorts; otherwise the typed declarations decide exactly as they do
with no order in scope, so `m ≤ n + 1` stays the natural order inside a
lattice section. With no typed declaration of the token in scope and no
supplying hypothesis the token is an error that names the shapes it
accepts. The target of a hypothesis predicate form becomes a transparent
guard, so a fact `a ≤ b` opens to `relates(le(P), a, b)` wherever local
evidence is consulted, and the target is a predicate of the area rather
than `relates` itself, which every order in the library states its facts
with. With two ordered sets in scope, as under `MonotoneMap(f, P, Q)`, the
operands choose by membership in a carrier or by being the value `f(a)` of
a function into one. Goals and statements print the forms back by
precedence, `≤` needing no parentheses inside a larger formula. A binder
`(a b : P)` under an order hypothesis is membership in `P.points`, the
carrier the predicate form names, as `(a : G)` is under a group.

The join and meet are set
functions on `points(P) × points(P)` determined by the order (`defgraph`
under `Lattice(P)`), so `sup.join` identifies `a ⊔ b` with the unbundled
`join(points(P), le(P), a, b)` and the closure instances `sup.member` and
`inf.member` give `a ⊔ b ∈ points(P)` from the memberships of `a` and `b`.
The bounds of a `BoundedLattice(P)` are the constants `⊥` and `⊤`, the
supremum and infimum of a subset `S` of the points the prefix forms `⨆ S`
and `⨅ S` of a `CompleteLattice(P)`, and the complement the postfix `aᶜ`
of a `BooleanAlgebra(P)`:

```g17 fragment
notation constant "⊥" => bot(P) via hypothesis BoundedLattice(P) for P.points
notation prefix 90 "⨆" => apply(sSup(P), _) via hypothesis CompleteLattice(P) for P.points
notation postfix 90 "ᶜ" => apply(compl(P), _) via hypothesis BooleanAlgebra(P) for P.points
```

A `constant` declared under a hypothesis is a term over its pattern
variables, read off the hypothesis in scope with no operands and printed
back as the token; it lies in the carrier named by `for`, so `⊥ ≤ a` is the
order of `P`. The carrier of a prefix form such as `⨆` is where its value
lies, its operand being a subset of it. A token may be a modifier letter
such as `ᶜ`, which ends the name it follows, so `aᶜᶜ` is accepted as the
complement twice and prints as `(aᶜ)ᶜ`, with the parentheses of print. The laws have short standard names such as `le_antisymm`, `sup_le`,
and `sup_comm`, each stated on carrier binders `(a b ∈ points(P))` in a
section whose hypothesis is the structure; `lattice_simp` is the rewrite
set of idempotency, absorption, associativity, and the bounds of a join and
a meet. A proof reads

```g17 fragment
theorem sup_comm (a b ∈ points(P))
  shows a ⊔ b = b ⊔ a
proof
  have first : a ⊔ b ≤ b ⊔ a := sup_le with (le_sup_right with *), (le_sup_left with *)
  have second : b ⊔ a ≤ a ⊔ b := sup_le with (le_sup_right with *), (le_sup_left with *)
  exact le_antisymm with *
```

with the lattice coming from the section hypothesis `lattice : Lattice(P)`.

### Spaces supplied by a hypothesis

Cumulus bundles a topological space as the structure `TopologicalSpace`
and a metric space as `MetricSpace`, and declares
`notation infix 50 "⇝" => Converges(X, _, _) via hypothesis TopologicalSpace(X) for X.carrier`
and, for a metric space,
`Converges(metricTopology(X), _, _) via hypothesis MetricSpace(X) for X.carrier`,
so `u ⇝ x` is convergence in whichever space the limit lies in, and a
binder `(x : X)` under either hypothesis is `x ∈ X.carrier`. A continuous
map is the transparent guard `notation guard "_ : _ ⇒ _" => Continuous`, so
a hypothesis `f : X ⇒ Y` supplies both spaces and the binders `(x : X)` and
`(y : Y)`; the guard is spelled with `⇒` because `⟶` is the hom of a
category. The distance between two points of a metric space is `d(x, y)`,
a [function supplied by the hypothesis](#functions-supplied-by-a-hypothesis)
that stands for the projection applied, `X.dist(x, y)`; under a
continuity, isometry, or Lipschitz hypothesis between two spaces the
arguments choose the space, so an isometry satisfies `d(f(x), f(y)) = d(x, y)`.
`topology_simp` is the rewrite set of the idempotent and distributive laws
of interior and closure, and `metric_simp` of the distance from a point to
itself and membership in balls.

### Dot notation on structures

A field of a [structure](datatypes.md#structures) is read with a dot:
`C.obj` is the projection `Category.obj(C)`, `C.dom(f)` applies the
projected function, `C.comp(g, f)` applies the projected operation to two
arguments, and `F.src.obj` chains projections. The spellings `obj(C)` and
`Category.obj(C)` denote the same term. The structure meant is decided by
the receiver, in this order: there is one structure in scope with the field;
a hypothesis in scope places the receiver in one, as `Category(C)`,
`Functor(F, C, D)`, the guard `F : C ⥤ D`, or any fact whose definition
already applies that structure's projections to the receiver, as
`IsProduct(C, …)` does; the receiver is built by a structure's constructor,
or by a definition whose body is one, as `opposite(C)` and
`identityFunctor(C)` are; or a soft-typed field names the structure of its
value. Otherwise the projection is ambiguous and the error names the
qualified spellings, so a plain `def` over a bare variable writes
`Category.obj(C)`. A declared function with a field's name keeps the bare
spelling, and the projection is reached by the dot or the qualified name.

Statements and goals print every projection in dot notation, `C.obj`,
`C.id(b) ∘ f`, `∀ a b ∈ C.obj`, when the receiver is a variable or a chain
of projections, and as `Category.obj(opposite(C))` on any other receiver;
the constructor prints as `Category.mk(…)` and the shape as
`Category.Data(C)`.

### How statements and goals are printed

Printing follows the declared precedences and omits the parentheses they
make redundant: `+` and `*` bind as declared (60 and 70, both grouping to the
left), powers to the right, and `2 * n + 2` or `(2 * n + 2) * (2 * n + 1)`
appear as written. A negation directly after an operator keeps its
parentheses, `x + (-x)`, and a prefix or postfix operator parenthesizes an
operand that binds more loosely, `-(a + b)` and `(n + 1)!`. Connectives
print the same way, `¬` tightest, then `∧`, `∨`, `→` (grouping to the
right), and `↔`; a quantifier on the right of a connective needs no
parentheses, since it extends to the end.

A soft-type guard is an ascription: on its own, `Nat(n)` prints as `n : ℕ`,
and `Integer`, `Rational`, and `Real` print as `ℤ`, `ℚ`, and `ℝ`. A
quantifier prefix whose guards follow its binders is printed with the guards
on the binders, grouped by sort: `∀ m, ∀ n, Nat(m) → Nat(n) → φ` prints as
`∀ m n : ℕ, φ`, and `∀ A, ∀ m, ∀ n, Nat(m) → Nat(n) → φ` as `∀ A, ∀ m n : ℕ,
φ`. Inside a larger formula a guard stays a predicate, as `Nat(n) ∧ P` is
clearer than `(n : ℕ) ∧ P`. A natural number bounded by an order is a
bounded quantifier: `∀ k ≤ n, φ` is `∀ k, Nat(k) → k ≤ n → φ` with `k` a
natural number in `φ`, `∃ k < n, φ` is `∃ k, Nat(k) ∧ k < n ∧ φ`, and both
print back in the bounded form when the bound does not mention the
variable. A subset is bounded the same way: `∀ X ⊆ V, φ` is
`∀ X, X ⊆ V → φ`, `∃ X ⊆ V, φ` is `∃ X, X ⊆ V ∧ φ`, several variables may
share one bound, and both print back as written. The formula is unchanged
by any of this; only its text is.

Two notations that share a token and fixity never share a spelling in one
printed formula: of the group power `x ^ n` and the matrix power under a
typed `^`, the declaration met first keeps the token and the other prints
by name, `groupPow(G, x, n)` or `matrixPow3(x, n)`. Two instances of one
declaration keep the token, since their operands tell them apart, as in
`f(a * b) = f(a) * f(b)` under `f : G →* H`. A graph applied to a pair
prints as the two-argument application, `f(a, b)`, the spelling of
`call2(f, a, b)`, and the set of natural numbers prints as `ℕ` wherever it
occurs; `ω` reads back to the same set.

All of this is independent of the `class` declaration form for possibly
proper mathematical collections. Tau proves operand predicates, instance
resolution selects operations and constants, and the kernel checks the
resulting term and proof. Variable names play no role in any of the three
steps.

Function codomains also feed soft-type reconstruction. Once the context
contains `FunctionBetween(f, ℝ, ℝ)` and `A : Real`, `typecheck` derives
`Real(apply(f, A))`; arithmetic and order notation on `f(A)` therefore select
the real instances without a function-specific typing lemma.
Application parentheses on a set variable or an already constructed function
elaborate to the same `apply` term as brackets. Declared function symbols
still take their own arguments: `realPow(A, n)` denotes the declared binary
function, while `f(x)` denotes application of the set `f`.

The ordered-pair forms elaborate identically, but they communicate different
intent. Use `(x, y)` for Cartesian-product elements, arbitrary relation pairs,
coordinates, tags, and structural encodings. Reserve `x ↦ y` for a graph entry
whose left side is being mapped to its right side. Theorems about a constructor
keep stable identifier names such as `singleton.membership`, `pair.membership`,
and `orderedPair.injective` even when their statements use `{x}`, `{x, y}`, and
`(x, y)`.

## Lists and reopened namespaces

`[a, b, c]` abbreviates the List constructors, and `a :: b :: xs`
is right-associative cons (precedence 55). Import `Grace.Core.List` for list
operations and their background theorems. See `datatypes.md`.

Within `namespace Euclidean`, write `Foo` to declare `Euclidean.Foo` and
refer to other imported declarations in that namespace without qualification.
Files can reopen the same namespace; a module name records provenance and
dependencies and is no part of the public name. Outside, use `Euclidean.Foo`
or `open Euclidean`. Two matching opened names are an ambiguity error;
`_root_.Euclidean.Foo` forces an absolute reference. Namespace-local opens end
with their namespace block.

A module may declare one name as a predicate or a function at two arities,
`Compact(X)` beside `Compact(X, A)`: the second declaration lives under the
namespace `arityN` of its module, `Grace.Cumulus.Topology.Structure.arity1.Compact`,
which is open wherever the module is, so a written name resolves by the
number of its arguments exactly as two declarations in different modules
do, and statements and goals print the plain name. A tactic naming the
predicate alone, `unfold Compact`, means the one the goal mentions, or the
fact named by `at`.

## Counted premise arguments

Write `with *{3}, edge` instead of `with assumption, assumption, assumption,
edge` when applying only part of a theorem. The count is an integer from 1 to
256 and expands to that many assumption entries, with no further proof search.
The same notation works with `specialize`. Bare `with *` stops at a named
source theorem's declared requirements. Local proof values have no such
boundary, so use a count when their remaining implication should be
preserved. See [tactics](tactics.md).

## Scoped ring operations

Inside a theorem section, write `notation ring R := (A, add, zero, neg, mul, one)`
to use algebra syntax for those operation graphs. Several rings can coexist,
with `R[expression]` to disambiguate, polynomial rings, quotients, and
restrictions are named `R[I]`, `P ⧸ J`, and `R ↾ T`, and a scope name stands
for its pieces in `IsField(R)`, `IsMaximalIdeal(P, M)`, or
`IsRingHom(e, P, R)`.
The declaration adds no hypotheses, axioms, or kernel operations. See
[ring scopes over separate pieces](algebra.md#ring-scopes-over-separate-pieces).

Which predicates and functions take a scope name is declared beside them,
not built in. The declaration

```g17 fragment
notation scoped IsIdeal(R, I) => IsIdeal(R.carrier, R.add, R.zero, R.neg, R.mul, I)
```

in the module that defines `IsIdeal` says that under a ring scope
`IsIdeal(R, I)` is the predicate at the scope's pieces, and the predicate
prints back in that form. The written parameters are pattern variables, and
each argument of the target is one of them passed through, or a piece of
one, `R.carrier`, `R.add`, `R.zero`, `R.neg`, `R.mul`, or `R.one`, which
must name an active scope; a parameter used only as `R.carrier` also
accepts an ordinary set. The target may be a predicate or a function. The
form is visible wherever the declaring module is imported, and a module
declares scoped forms for its own predicates and functions the same way.
