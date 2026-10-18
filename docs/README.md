# Grace17 documentation

Start with the [introduction](introduction.md). It explains why Grace17 is
built on set theory, walks through first proofs, and tours the larger
developments in Cumulus.

## Language

- [Definitions](definitions.md): `def`, `predicate`, `class`, recursion, and their proof obligations
- [Ordinals](ordinals.md): von Neumann ordinals and executable Cantor normal forms
- [Datatypes](datatypes.md): inductively defined classes of sets, and `structure` declarations for groups, rings, orders, and categories
- [Types and instances](types.md): soft types, classes, and instance resolution
- [Notation](notation.md): mathematical notation, Unicode and ASCII, and `notation` declarations
- [Proving theorems](proving.md): writing statements and proofs, applying theorems, and using the automation
- [Tactic reference](tactics.md): every tactic, organized as in the Workbench Help, with examples and rule schemas
- [Modules, namespaces, and sections](modules.md): how files, imports, names, and shared hypotheses organize a development

## Cumulus, the mathematics library

- [Cumulus guide](cumulus.md): what is proved, organized by subject
- [Top 100 theorems](top-100.md): formal statements and proof links
- [Erdős problem 397](erdos-397.md): an infinite family of binomial coincidences, found with an AI, checked from the axioms
- [Algebraic hierarchy](algebra.md): how structures are represented
- [Axiom audits](axiom-audit.md): inspecting Choice and other assumptions a proof uses

## Community

- [Community](community.md): Zulip chat, GitHub, how to cite, and how to contribute mathematics

## Trust

- [Foundations](foundations.md): the foundation contract and the ZF, ZFC, and ZFG profiles
- [Natural deduction certificates](natural-deduction.md): every proof as a Fitch-style or Gentzen-style derivation you can read
- [Soundness](soundness.md): what is trusted, independent checkers, and the path to proved checkers
- [Checker semantics](checker-semantics.md): the proof checker as a small-step transition system, the definition every independent checker implements
- [Kernel format](kernel-format.md): the normative G17M proof-tape specification
- [Compiled module format](compiled-module-format.md) and [foundation bootstrap](foundation-bootstrap.md): G17C
- [Conformance](conformance.md): the executable compatibility corpus for checkers
- [Ground evaluation](ground-evaluation.md): the trusted evaluator behind `compute`
- [Independent checkers](../checkers/README.md): the Python, OCaml, and Rust checkers

## For AI agents

- [Grace17 for AI agents](agents.md): the checking API, goal states, search, and a working loop for agents that prove theorems
- [Machine interface](machine-interface.md): `g17 serve` and the method subcommands, the JSON protocol that exposes what the Workbench shows
- Claude Code users: `/plugin install grace17 --marketplace grace17-prover/grace17` installs the Grace17 skill
- [AGENTS.md](../AGENTS.md): expectations for coding agents that modify Grace17 itself

## Tooling

- [Architecture](architecture.md): how the system fits together, for people working on Grace17 itself
- [Workbench](workbench.md): the browser proof assistant
- [Library search](library-search.md)
- [External libraries](external-libraries.md): developing mathematics outside the Grace17 checkout
- [Website](website.md): building the static site, Cumulus browser, and embedded Workbench
