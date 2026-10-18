# Modules, namespaces, and sections

A Grace17 development is organized at three scales. A **module** is a file:
it names itself, imports other modules, and exports its declarations. A
**namespace** controls the names of declarations, so that `Multigraph.EulerTrail`
and `primes.infinite` can live side by side without colliding. A **section**
shares variables and hypotheses across a family of theorems without changing
their names. A first proof needs only the first two lines of a file; the rest
of this page is for developments that grow.

## Modules and imports

A file under a module root is the module its path denotes:
`lib/Grace/Cumulus/Real/FiniteSum.g17` is `Grace.Cumulus.Real.FiniteSum`. Its
`module` line may spell that name out, as Cumulus does, or give just
`FiniteSum`; either way it must agree with the path.

```g17 fragment
module Grace.Cumulus.Real.FiniteSum
import Power
import Nat.Subtraction
```

An `import` is resolved relative to the importing module, innermost first:
from `Grace.Cumulus.Real.FiniteSum`, `import Power` finds
`Grace.Cumulus.Real.Power`, and `import Nat.Subtraction` finds
`Grace.Cumulus.Nat.Subtraction`. A fully qualified name such as
`import Grace.Cumulus.Main` always works. A file outside every module root
keeps the explicit form: its `module` line is its whole name, and it imports
by full names.

Subject entry points such as `Grace.Cumulus.Nat`, `Grace.Cumulus.Real`, and
`Grace.Cumulus.NumberTheory` import a subject's implementation graph and
re-export its public names, so a proof file imports one module and writes
mathematics. `Grace.Cumulus.Main` is the compact default environment, and
`Grace.Cumulus` is the complete library. The entry points for each subject
are listed under [getting started](cumulus.md#getting-started) in the
Cumulus guide.

Imports are acyclic, and a module is checked once and reused by every
importer. The command line and the Workbench need only the module root
`lib/`; see [external libraries](external-libraries.md) for developing
mathematics outside the Grace17 checkout with a module root of your own.

## Namespaces

Every module opens a namespace named after itself. The declarations of
`Grace.Cumulus.Real.FiniteSum` are `Grace.Cumulus.Real.FiniteSum.realPartialSum`
and so on, and an importer may write `realPartialSum` or
`FiniteSum.realPartialSum`. There is nothing to declare for this; a module's
namespace is its name.

A `namespace` block nests a further name under the module's:

```g17 fragment
module Grace.Cumulus.GraphTheory.Multigraph

namespace Multigraph

predicate EulerTrail (G t : Set) := ...

end Multigraph
```

Inside the block the predicate is `EulerTrail`; everywhere else it is
`Multigraph.EulerTrail`. Dotted declaration names do the same thing one name
at a time: `theorem primes.infinite` declares `infinite` inside `primes`, and the
usual convention is that laws about a definition `foo` are named `foo.law`.
Both spellings nest under the current namespace, so a namespace never has to
be qualified from the module's root. The rare escape hatch is `_root_`:
`namespace _root_.X` extends the namespace `X` from any module, which Cumulus
itself never needs.

An import makes a checked module available, but it does not automatically
put every name from that module into the short-name scope. `open M` makes the
public names in `M` available without qualification while checking the
current module only. `export open M` does the same locally and also makes that
opening part of the current module's public interface:

```g17
module My.OrdinalTools
import Grace.Cumulus.Set.Ordinal
export open Grace.Cumulus.Set.Ordinal
```

A later module that imports `My.OrdinalTools` may use the public names from
`Grace.Cumulus.Set.Ordinal` without their full qualification. This is how the
subject entry points compose their public scopes. A plain `open` never leaks
to importers, and neither form bypasses module imports.

When two visible declarations share a short name, the name is ambiguous and
the checker says which qualified names would resolve it. Keep names distinct
across the modules a development imports; distinct names are also what make
hover, search, and `exact?` useful.

## Theorem sections

Sections let you declare a mathematical context once and reuse it across a
family of theorems. They are especially useful when many results concern the
same ring, space, function, or collection of hypotheses.

The complete runnable introductory example is
[TheoremSections.g17](../examples/TheoremSections.g17); a larger algebra example is
[IdealCorrespondenceStarter.g17](../examples/IdealCorrespondenceStarter.g17).

### A shared context

```grace17
import Grace.Cumulus.Set

section Membership
variable (A x : Set)
hypothesis hx : x ∈ A

theorem member
  shows x ∈ A
proof
  exact hx

end Membership
```

Inside the section, `A`, `x`, and `hx` are available to every theorem. The
exported theorem means the same as this declaration:

```grace17
theorem member (A x : Set)
  requires hx : x ∈ A
  shows x ∈ A
proof
  exact hx
```

So `hypothesis` introduces a premise, and the kernel checks the universally
quantified implication. A hypothesis is a premise, never an axiom. Closing
the section removes its local context; the checked theorem remains available.

### Nested sections

You can add assumptions for just part of a development:

```grace17
section Membership
variable (A x : Set)
hypothesis hx : x ∈ A

section Pair
variable (y : Set)
hypothesis hy : y ∈ A

theorem both
  shows x ∈ A ∧ y ∈ A
proof
  refine ⟨hx, hy⟩
end Pair

theorem member_again
  shows x ∈ A
proof
  exact hx
end Membership
```

`both` exports parameters `A, x, y` and premises `hx, hy`.
`member_again` exports only `A, x` and `hx`: the inner context has ended.
The theorem `both` itself remains available after either section ends.

### Applying the exported theorem

Outside the section, supply its parameters and premises as usual:

```grace17 fragment
theorem use_both (B a b : Set)
  requires ha : a ∈ B
  requires hb : b ∈ B
  shows a ∈ B ∧ b ∈ B
proof
  exact both at B, a, b with ha, hb
```

Section variables precede theorem-local variables; outer section variables
precede inner ones. Inherited hypotheses precede theorem-local `requires`.
The `at` arguments follow that parameter order. Normal theorem-application
features still work, including `with *` and inference from named premises when
those premises determine all the required parameters.

For a source theorem, `exact theorem with *`
(or `show P := theorem with *`, or `have h := theorem with *`) can omit `at`:
the conclusion is matched against the goal when there is one, then uniquely
matching local premises determine the remaining parameters. Matching is
structural, indexed by formula head, and capped at 2,048 attempts. It does not
unfold definitions, backchain, or choose between ambiguous substitutions.
Typed parameters, including `Nat` and dependent `List(A)` binders,
participate through their generated guard requirements, and every guard still
needs evidence. An `at` list is the fallback.

This goal-directed path does not apply to unstated `have h := ...`, `apply`,
equivalence directions, or counted stars. Named-premise inference and
explicit arguments remain available there.

**All declared shared variables and hypotheses are exported, even unused
ones.** Keep broadly useful assumptions in the outer section and stronger ones
in a smaller nested section. Unused context is never removed for you.

### A typical algebra workflow

Declare the mathematical objects, then share their laws. A `def` or
`predicate` may also stand inside a section: it takes the section variables
as its leading parameters, in order, and is applied without them inside the
section, so `def lfp (f : Set) : Set := …` under `variable (P : Set)` is
`lfp(f)` there and `lfp(P, f)` everywhere else.


```grace17 import=Grace.Cumulus.Algebra.Ring
section RingMaps
variable (f A add zero neg mul one B plus z minus times unit : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
hypothesis target : IsCommRing(B, plus, z, minus, times, unit)
hypothesis hom : IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)

theorem inverse_image (J : Set)
  requires ideal : IsIdeal(B, plus, z, minus, times, J)
  shows IsIdeal(A, add, zero, neg, mul, idealComap(f, A, J))
proof
  exact IsRingHom.comap_ideal with source, target, hom, ideal

end RingMaps
```

This excerpt uses `import Grace.Cumulus.Algebra.Ring`. The worked algebra example
also introduces surjectivity in an inner section, so the inverse-image results
do not pick up a surjectivity premise they do not need. For another example
of keeping hypotheses minimal, see
[PrimeCorrespondenceStarter.g17](../examples/PrimeCorrespondenceStarter.g17):
prime inverse images are proved in the outer ring-map section, while maximal
inverse images and both equivalences use an inner surjectivity section.

### Sections and namespaces

A section controls local context; a namespace controls declaration names.
`section Membership` does not add `Membership` to a theorem's name. Inside
`namespace SectionExamples`, the theorem above is `SectionExamples.member`;
within that namespace it can be referred to as `member`.

Use a namespace around sections when both naming and shared context are wanted.
Close a section before starting another namespace. Ending a section inside a
namespace leaves that namespace active.

### Syntax and current boundaries

| Form | Meaning |
| --- | --- |
| `section Name` | Begin a named theorem context. |
| `variable (A x : Set)` | Add variables using binder syntax. |
| `hypothesis hx : x ∈ A` | Add a named shared premise. |
| `end Name` | End the innermost section; the name must match. |
| `end` | End the innermost section without repeating its name. |

- Sections support `theorem`, `lemma`, and `instance` declarations. Definitions,
  imports, namespace declarations, and `export open` belong outside sections.
- Plain `open` directives may appear inside a section; their scope is restored
  when the section ends.
- Write each `hypothesis` declaration on one line. Its variables must already
  be in scope when it is declared.
- Variable and hypothesis names must be distinct throughout the active context;
  theorem-local binders and premises must not collide with inherited names.
- `variable` and `hypothesis` require an active section. Missing ends and
  mismatched named ends are errors.

The Workbench highlights these commands and provides declaration help on hover.
Proof and goal-history locations retain their original source lines. Editing a
shared hypothesis invalidates affected cached theorem checks.

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

For tactic applications see [tactics.md](tactics.md); for definitions see
[definitions.md](definitions.md); for proofs see [proving.md](proving.md).
