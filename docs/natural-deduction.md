# Natural deduction certificates

Every theorem Grace17 accepts comes with a proof the kernel has checked: a
derivation in natural deduction for first-order logic with equality, from the
ZF(C/G) axioms and the theorems already admitted. Tactics, proof search,
`ring`, and AI agents only ever produce such derivations, and the kernel
admits a theorem by checking its derivation from scratch. The Workbench shows
the derivation of any theorem under **Kernel proof**, and the ones on this
page are rendered from the same checked certificates.

## Two pictures of one derivation

A natural-deduction derivation is a tree of inferences. In Gentzen's
presentation the premises of a rule stand above a bar and its conclusion
below, assumptions are leaves, and a rule such as →I or ∀I discharges the
assumptions it closes over, which the tree shows in brackets. Fitch's
presentation writes the same derivation as a numbered list: every line cites
earlier lines, an assumption opens a subproof marked by a vertical rail, and
the rule that discharges it cites the whole span.

The kernel stores a derivation as a directed graph of judgments Γ ⊢ φ in
which a shared subproof appears once. The Fitch rendering lists each judgment
once, premises before conclusions; the Gentzen rendering unfolds the graph
into a tree, so a shared subproof is drawn wherever it is used. Select a
Fitch line to see its inference as a rule with premises, conclusion, any
freshness side condition, and the exact kernel arguments.

The first proof of the [introduction](introduction.md) is three lines of
Grace17 and fourteen kernel lines:

```g17-proof file=examples/Introduction.g17 theorem=Introduction.subset_step style=both
A subset fact unfolds to a universal implication, which is instantiated and applied.
```

A proof that reasons about union membership:

```g17-proof file=lib/Grace/Cumulus/Set/Core.g17 theorem=union.subset style=both
```

## What automation leaves behind

Automation is not trusted; it is checked. The integer identity below is
closed by `ring` in one line of Grace17, and what `ring` hands to the kernel
is a derivation of a few hundred steps, each one an ordinary inference. The
list is folded; open any line.

```g17-proof file=examples/Introduction.g17 theorem=Introduction.difference_of_squares style=fitch
Every step is one rule of logic or one ring axiom applied to earlier lines.
```

The principle of mathematical induction in Cumulus
([natural.induction](../lib/Grace/Cumulus/Nat/Induction.g17)) is twenty lines
of tactics and about nine hundred kernel lines; open its derivation in the
Workbench to read it.

## Reading derivations in the library

Every module page of [Cumulus](../lib/Grace/Cumulus/Set/Core.g17) lists its
theorems with a **derivation** link. The link opens the module in the
Workbench, checks it in your browser, and opens the **Kernel proof** drawer
at that theorem. Nothing is sent to a server, and the derivation you read is
the one the kernel checked a moment earlier.

The same certificates are what the independent checkers verify. The
[kernel format](kernel-format.md) is their specification, and
[soundness](soundness.md) describes what is trusted.
