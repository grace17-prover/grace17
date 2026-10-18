# Erdős problem 397, checked from the axioms

In 1980 Erdős and Graham asked whether the equation

```text
∏ᵢ C(2mᵢ, mᵢ) = ∏ⱼ C(2nⱼ, nⱼ)
```

has only finitely many solutions in which all the indices `mᵢ` and `nⱼ` are
distinct positive integers. It is problem 397 in
[Thomas Bloom's database of Erdős problems](https://www.erdosproblems.com/397).
In January 2026 Neel Somani, working with ChatGPT, found that the answer is
no: for every `a ≥ 2`, with `c = 8a² + 8a + 1`,

```text
C(2a, a) · C(4a + 4, 2a + 2) · C(2c, c) = C(2a + 2, a + 1) · C(4a, 2a) · C(2c + 2, c + 1).
```

The database records the problem as resolved, and further families were
found afterwards by other contributors. The argument is short, and it is
exactly the kind of claim an independent checker should be able to confirm
without taking anyone's word for it. Cumulus proves the family from the
axioms of ZF; the module is
[`Grace.Cumulus.NumberTheory.Erdos397`](../lib/Grace/Cumulus/NumberTheory/Erdos397.g17),
and `tests/erdos-397.test.ts` audits every theorem it uses for admissions and
for Choice, finding neither.

## What is proved

Binomial coefficients are defined by Pascal's rule in
[`Grace.Cumulus.NumberTheory.Binomial`](../lib/Grace/Cumulus/NumberTheory/Binomial.g17),
and the central coefficient is `central(n) = 2 * n choose n`.

<!-- cumulus-source: lib/Grace/Cumulus/NumberTheory/Erdos397.g17 -->
```g17
theorem erdos397.identity (a : Nat)
  shows central(a) * (central(2 * a + 2) * central(8 * a * a + 8 * a + 1)) =
    central(a + 1) * (central(2 * a) * central(8 * a * a + 8 * a + 2))
```

For `a ≥ 2` the three indices on each side are distinct, and the two sides
use different indices, so each `a` is a solution in the sense of the problem.

<!-- cumulus-source: lib/Grace/Cumulus/NumberTheory/Erdos397.g17 -->
```g17
theorem erdos397.distinct (a : Nat)
  requires large : 2 ≤ a
  shows (a ≠ 2 * a + 2 ∧ a ≠ 8 * a * a + 8 * a + 1 ∧
      2 * a + 2 ≠ 8 * a * a + 8 * a + 1) ∧
    (a + 1 ≠ 2 * a ∧ a + 1 ≠ 8 * a * a + 8 * a + 2 ∧
      2 * a ≠ 8 * a * a + 8 * a + 2) ∧
    (a ≠ a + 1 ∧ a ≠ 2 * a ∧ a ≠ 8 * a * a + 8 * a + 2)
```

Beyond any bound there is another solution, which is the negative answer to
the question as asked.

<!-- cumulus-source: lib/Grace/Cumulus/NumberTheory/Erdos397.g17 -->
```g17
theorem erdos397.unbounded (N : Nat)
  shows ∃ a ∈ ℕ, N < a ∧ 2 ≤ a ∧
    central(a) * (central(2 * a + 2) * central(8 * a * a + 8 * a + 1)) =
    central(a + 1) * (central(2 * a) * central(8 * a * a + 8 * a + 2))
```

## How the proof goes

Everything rests on one step law for central binomial coefficients,

```text
C(2n + 2, n + 1) · (n + 1)² = C(2n, n) · (2n + 2)(2n + 1),
```

which follows from the factorial form `choose(n + k, k) · k! · n! = (n + k)!`,
itself proved by induction from Pascal's rule. Applying the step law at `a`,
`2a`, `2a + 1`, and `c`, multiplying the claimed identity by the nonzero
product `(a + 1)²(2a + 1)²(2a + 2)²(c + 1)²`, and rewriting with the four
instances leaves a polynomial identity in `a` of degree ten, which `ring`
settles once `c + 1 = 2(2a + 1)²` and `2c + 1 = (4a + 3)(4a + 1)` have done
their work inside it. Cancelling the product gives the identity. The
distinctness claims are linear arithmetic over the naturals, with `a²` as an
atom.

The proof is checked by the kernel like every other theorem in Cumulus, and
the independent Python, OCaml, and Rust checkers replay the exported certificate.
Nothing here depends on the discovery process: the family could have come
from a person, a search, or a language model, and the check would be the same.

## Trying it

[Erdos397Starter.g17](../examples/Erdos397Starter.g17) computes a few central
binomial coefficients and instantiates the family at `a = 2`, where it reads
`C(4, 2) · C(12, 6) · C(98, 49) = C(6, 3) · C(8, 4) · C(100, 50)`. Open it in
the Workbench, change the `2`, and check again.
