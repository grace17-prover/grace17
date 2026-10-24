# The cycle double cover theorem: blueprint

Every bridgeless graph has a list of cycles such that every edge lies in
exactly two of them. This blueprint plans its formalization in Cumulus as
checked Grace17 modules: every definition here is final, every theorem is
stated in full and admitted with `sorry`, and the import graph is the
dependency graph of the proof. The blueprint checks as it stands; filling
it in replaces admissions with proofs, one theorem at a time, and
`npm run blueprint:status` reports what remains.

```sh
npm run blueprint:check     # the whole blueprint elaborates
npm run blueprint:status    # theorems per module, proved and admitted
```

The module root is `blueprints/`; the modules are `CycleDoubleCover.*`.
A module whose last admission goes is promoted into Cumulus under the home
named in its header, with its module line renamed and its imports made
relative, and is then held to the Cumulus rules: at most three imports for a
proof module, headers, and no admissions.

## The proof

The source is Sang-il Oum's exposition of the July 2026 proof
(arXiv 2607.16356), with one change of route. The exposition reduces to
cubic 3-edge-connected graphs by a minimal counterexample, which rests on
Fleischner's splitting lemma; we instead expand every vertex of degree d
into a d-cycle, which makes the graph cubic without changing whether it is
bridgeless, and reduce the eight-flow theorem to the 3-edge-connected case
by contracting an edge of a cut of two edges. Both theorems the exposition
assumes are proved here: tree packing by Kaiser's elementary argument
(arXiv 0911.2809), and the eight-flow theorem from it.

1. **Graphs.** Edge sets of the existing multigraph model
   `Graph(V, E, leftEnd, rightEnd)` as a parity algebra: the degree of a
   vertex in an edge set counts edge ends, a loop contributing both; even
   edge sets are closed under symmetric difference; an even edge set crosses
   every cut an even number of times, so a bridge lies in no even edge set.
   Connectivity along an edge set, partitions of the vertex set and the
   quotient multigraph of a partition, forests and spanning trees with the
   fundamental even set and the one-edge exchange.
2. **Tree packing.** A k-decomposition is a colouring of the edges with k
   colours; the packing condition asks every partition of V to be joined by
   k(|P| − 1) edges. Kaiser's proof refines the trivial partition along the
   colours until every colour is internally connected, assigns each edge the
   level at which its ends part, and exchanges an edge of least level in a
   cycle of the last colour for one of lower level; the exchange improves the
   decomposition in a well-founded order, so a maximal decomposition packs.
   Corollaries: a 2k-edge-connected graph packs k trees; doubling every edge,
   a 3-edge-connected graph has three spanning trees with no common edge.
3. **Parity systems.** Linear algebra over the two-element field in the
   language of finite sets: a matrix is a relation between rows and columns,
   a vector a set of coordinates, and a row equation asks for the parity of a
   finite set. The alternative, that a system is solvable exactly when no
   left-kernel vector sees an odd right-hand side, is proved by eliminating
   one column at a time. This replaces the dimension argument of the
   exposition's consistency criterion and needs no vector-space theory.
4. **Flows.** A nowhere-zero flow in three copies of the two-element field is
   three even edge sets covering every edge; the value of an edge is the set
   of coordinates whose even set holds it. Three spanning trees with no
   common edge give one, by the even superset of each tree's complement;
   contracting an edge of a two-edge cut keeps a graph bridgeless and lifts a
   cover; so every finite bridgeless graph has one.
5. **Double covers.** Two-element labels on the edges with even local
   multiplicity give an even double cover; a cubic loopless graph with an
   even cover has such labels, by the compatibility system for the vertex
   vectors and the dual obstruction computation of the proof; a rotation
   system expands a bridgeless graph into a cubic bridgeless one; an even
   double cover of the expansion projects back; and every even edge set
   splits into cycles.

## Modules

| module | layer | planned home in Cumulus |
|---|---|---|
| Graphs.EdgeSets | 1 | Cardinal/Parity |
| Graphs.Degree | 1 | GraphTheory/Multigraph/Degree |
| Graphs.Even | 1 | GraphTheory/Multigraph/Even |
| Graphs.Cuts | 1 | GraphTheory/Multigraph/Cuts |
| Graphs.Connectivity | 1 | GraphTheory/Multigraph/Connectivity, Quotient |
| Graphs.Trees | 1 | GraphTheory/Multigraph/Trees |
| TreePacking.Decompositions | 2 | GraphTheory/TreePacking/Decompositions |
| TreePacking.Kaiser | 2 | GraphTheory/TreePacking/Kaiser |
| TreePacking.Corollaries | 2 | GraphTheory/TreePacking/Corollaries |
| Parity.Systems | 3 | Combinatorics/ParitySystems |
| Flows.EvenCovers | 4 | GraphTheory/Flows/EvenCovers |
| Flows.Contraction | 4 | GraphTheory/Flows/Contraction |
| Flows.EightFlow | 4 | GraphTheory/Flows/EightFlow |
| DoubleCover.Covers | 5 | GraphTheory/DoubleCover/Covers |
| DoubleCover.CubicLabeling | 5 | GraphTheory/DoubleCover/CubicLabeling |
| DoubleCover.Expansion | 5 | GraphTheory/DoubleCover/Expansion |
| DoubleCover.Theorem | 5 | GraphTheory/DoubleCover/Theorem |

```mermaid
graph TD
  EdgeSets --> Degree --> Even --> Cuts --> Connectivity --> Trees
  Trees --> Decompositions --> Kaiser --> Corollaries
  EdgeSets --> Systems
  Trees --> EvenCovers --> Contraction --> EightFlow
  Corollaries --> EvenCovers
  Trees --> Covers
  Covers --> CubicLabeling
  EvenCovers --> CubicLabeling
  Systems --> CubicLabeling
  Covers --> Expansion
  Cuts --> Expansion
  CubicLabeling --> Theorem
  Expansion --> Theorem
  EightFlow --> Theorem
```

## Conventions

- Statements name the graph by its four parts, as `Multigraph` does, and
  take finiteness and `Graph(V, E, leftEnd, rightEnd)` as hypotheses rather
  than building them into predicates, so each lemma says what it uses.
- Vectors over the two-element field are finite sets: the sum is `△`, the
  dot product the parity of the intersection, the span of p is `{∅, p}`.
  Flow values are subsets of `3`, label values subsets of `𝒫(3)`.
- Proofs follow the Cumulus style: readable steps, Unicode notation, lines
  within 80 columns where practical, and no proof much longer than its
  informal counterpart. Helper lemmas belong beside the statement they serve.
- Each agent works through the machine interface on one module at a time,
  never edits another module's statements, and reports ergonomic friction
  rather than working around it in the proof.

## Status

<!-- blueprint-status -->
| module | theorems | proved | admitted |
|---|---:|---:|---:|
| CycleDoubleCover.Graphs.EdgeSets | 5 | 5 | 0 |
| CycleDoubleCover.Graphs.Degree | 24 | 24 | 0 |
| CycleDoubleCover.Graphs.Even | 5 | 5 | 0 |
| CycleDoubleCover.Graphs.Cuts | 24 | 24 | 0 |
| CycleDoubleCover.Graphs.Connectivity | 27 | 27 | 0 |
| CycleDoubleCover.Graphs.Trees | 48 | 48 | 0 |
| CycleDoubleCover.DoubleCover.Covers | 4 | 0 | 4 |
| CycleDoubleCover.TreePacking.Decompositions | 5 | 0 | 5 |
| CycleDoubleCover.TreePacking.Kaiser | 9 | 0 | 9 |
| CycleDoubleCover.TreePacking.Corollaries | 5 | 0 | 5 |
| CycleDoubleCover.Flows.EvenCovers | 5 | 0 | 5 |
| CycleDoubleCover.Parity.Systems | 3 | 0 | 3 |
| CycleDoubleCover.DoubleCover.CubicLabeling | 5 | 0 | 5 |
| CycleDoubleCover.DoubleCover.Expansion | 8 | 0 | 8 |
| CycleDoubleCover.Flows.Contraction | 5 | 0 | 5 |
| CycleDoubleCover.Flows.EightFlow | 4 | 0 | 4 |
| CycleDoubleCover.DoubleCover.Theorem | 2 | 0 | 2 |
| **total** | **188** | **133** | **55** |
<!-- /blueprint-status -->
