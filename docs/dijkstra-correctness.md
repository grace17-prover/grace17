# Dijkstra: complete mathematical correctness argument

This is a mathematical proof for the executable algorithm in `Dijkstra.g17`.
The complete executable correctness theorem is formalized in Grace17.
The sections at the end map this argument to its checked proof terms.

## Statement and representation assumptions

Let `count = n` be a natural number, with vertices `V = {0, …, n−1}` and
`source = s ∈ V`. Let `rows` be an `n × n` matrix whose entries are either
`Option.none` or `Option.some(w)` for a natural weight `w`. An entry `some(w)`
at `(u,v)` represents the directed edge `u → v` of weight `w`; `none`
represents its absence. The graph's edge set and weight function agree with
these entries.

For `result = Dijkstra.solve(n, s, rows)`, and each `v ∈ V`:

1. If `entry(distances(result), v) = some(d)`, then a path from `s` to `v`
   has cost `d`, and every such path has cost at least `d`.
2. `entry(distances(result), v) = none` if and only if no path from `s` to
   `v` exists.

Paths may repeat vertices; all their costs are sums of natural edge weights.
In particular, this statement includes zero-weight edges, cycles, ties, and
vertices unreachable from the source. The source-in-range assumption excludes
an empty vertex set. There is no assertion here for malformed matrices or an
out-of-range source.

## State invariant

Write `D(v)` for the optional tentative distance at index `v`, treating `none`
as infinity. Write `S` for the vertices whose settled flag is `1`. Order finite
labels by natural order, put every finite label below infinity, and define
`min` using this extended order.

Immediately before each call of `advance`, maintain:

- **Shape:** the distance and flag vectors have length `n`; all distances are
  optional naturals and all flags are natural numbers; only `1` means settled.
- **Witnesses:** if `D(v)` is finite, its value is the cost of a path from
  `s` to `v`.
- **Settled correctness:** every `u ∈ S` has a finite distance, and `D(u)` is
  a globally shortest path cost from `s` to `u`.
- **Relaxed boundary:** for every edge `u → v` of weight `w`, with `u ∈ S`
  and `v ∉ S`, `D(v) ≤ D(u) + w`. Since the right side is finite, this
  condition also asserts that `D(v)` is finite.
- **Source:** `D(s) = 0`.

Initially `S` is empty, `D(s)=0`, and every other distance is infinity. Shape
holds by construction. The zero-edge path witnesses the source label; there
are no other finite labels. Settled correctness and the boundary condition
are vacuous. Thus all five clauses hold initially.

## The greedy choice is globally shortest

Suppose the scan returns a finite candidate `(x,d)`. The scan theorems establish
that `x ∈ V \ S`, `D(x)=d`, and `d ≤ D(v)` for every finite open label.
The witness invariant supplies a path to `x` of cost `d`.

Consider any competing path from `s` to `x`, of cost `c`.

If `s ∉ S`, then the source is an open candidate of cost zero, so `d ≤ 0`.
Naturality gives `d=0`, and nonnegative path costs give `d ≤ c`.

If `s ∈ S`, the competing path starts in `S` and ends outside `S`. Choose
its first vertex `v` outside `S`, and let `u` be the preceding vertex. Let
`p` be the cost of the path prefix ending at `u`, and `w` the weight of its
next edge `u → v`. Settled correctness and the relaxed boundary give

```
D(u) ≤ p,
D(v) ≤ D(u) + w ≤ p + w ≤ c.
```

The final inequality uses nonnegative weights on the remaining suffix.
The boundary condition makes `D(v)` finite; `v` is open, so scan minimality
also gives `d ≤ D(v)`. Hence `d ≤ c`.

This holds for every competing path. Together with the witness of cost `d`,
it proves that `d` is globally shortest for `x`.

## Preservation by the executable update

The algorithm first marks `x`, giving `S' = S ∪ {x}`, then relaxes the row of
`x`. Pointwise:

- For `v ∈ S'`, leave `D(v)` unchanged.
- For `v ∉ S'` with no edge from `x`, leave `D(v)` unchanged.
- For `v ∉ S'` with edge weight `w`, set `D'(v) = min(D(v), d+w)`.

The checked indexed relaxation equation establishes this correspondence to
the recursive vector implementation. Marking preserves length and changes
only the selected flag. Relaxation preserves length and optional-natural
typing. Marking writes the natural number 1 and preserves vector length, proving shape.

Every finite updated label has a witness: either its old witness, or the
witness to `x` extended by the edge being relaxed. This proves the witness
clause. Old settled labels are unchanged; the new settled label is the
just-proved shortest label of `x`. Thus settled correctness is preserved.

For the boundary condition, take `v ∉ S'`:

- If `u ∈ S`, the old boundary condition applies, and relaxation never
  increases `D(v)`. Also `D'(u)=D(u)`. Consequently
  `D'(v) ≤ D(v) ≤ D(u)+w = D'(u)+w`.
- If `u=x`, the row relaxation gives `D'(v) ≤ d+w = D'(x)+w`.

These are all cases of `u ∈ S'`. Finally, a settled source is unchanged. An
open source starts with label zero and cannot increase during relaxation;
its updated finite natural label is therefore still zero. The source clause
is preserved as well.

If the scan returns `none`, `advance` leaves the state unchanged, so all
invariant clauses are immediately preserved.

## Why the fixed fuel suffices

Initially exactly `n` flags are open. Every successful advance settles a
previously open vertex and changes no other flag, reducing the open count by
one. A scan returning `none` is a fixed point for all remaining iterations.
Thus, after `n` iterations, either a fixed point was reached earlier or all
vertices have been settled. In either case there is no finite open label.

This argument is checked for the recursive executor as
`Dijkstra.solve.exhausts_finite_frontier`, under its row-typing premise. That
theorem alone does not give shortest-path correctness; the state invariant
supplies the connection.

## Extracting the result

Let the state after the fixed number of iterations be final. The invariant
holds by initialization and preservation, and no finite label is open.

Every finite label therefore belongs to a settled vertex. Settled correctness
says it is globally shortest; the witness clause says a path attains it.

Now suppose `D(v)=none` but a path from `s` to `v` exists. The source has finite
label zero and is therefore settled in the final state. The endpoint is not
settled, since all settled labels are finite. On the alleged path take the
first vertex outside the final settled set. Its predecessor is settled, so
the boundary condition gives it a finite label. It is also open, contradicting
final frontier exhaustion. Thus a vertex labeled `none` is unreachable.

Conversely, an unreachable vertex cannot have a finite label, because every
finite label has a path witness. Shape says its label is an optional natural,
so its label must be `none`. This proves both directions and completes the
mathematical correctness argument.

## Checked statement

The main theorem is
`Grace.Cumulus.GraphTheory.DijkstraCorrectness.Dijkstra.solve.correct`.
It is imported by the Cumulus graph-theory entrypoint.

Let `count`, `source`, and `target` be natural numbers, with source and target
in `Dijkstra.Vertices(count)`. Assume
`Dijkstra.MatrixRepresents(count, rows, E, weights)`. For
`result = Dijkstra.solve(count, source, rows)`, the theorem proves:

- For every natural distance `d`,
  `entry(distances(result), target) = some(d)` **if and only if**
  `ShortestPathCost(Vertices(count), E, weights, source, target, d)`.
- `entry(distances(result), target) = none` **if and only if**
  there is no natural cost of a path from source to target.

`ShortestPathCost` includes a path witness and a lower bound on every other
path cost. Paths may repeat vertices. The theorem therefore covers cycles,
ties, zero-weight edges, and unreachable vertices. Weights are natural
numbers. Source-in-range excludes an empty vertex set. Nothing is claimed for
an out-of-range source.

Matrix agreement requires typed rows and a weighted graph on the vertex set.
Within that set, an executable matrix lookup equals `some(k)` when and only
when there is an edge of weight `k`. Extra matrix padding is permitted. The
proof is about the executable solver itself; it does not substitute a
reference algorithm.

## Proof structure

`DijkstraInvariant.g17` defines the invariant over the executable accessors:
typed vectors of the right lengths, source label zero, witnesses for finite
labels, shortest finite labels for settled vertices, and a relaxed frontier.
Only flag value 1 means settled; the proof requires natural flags, without a
separate binary-flag invariant. Initialization is checked there.

`DijkstraCorrectness.g17` adds one predicate and eighteen theorems:

1. `OpenLowerBound` expresses a bound on finite open labels.
   `minimum.open_lower_bound` derives it from the checked scan semantics.
2. `StateInvariant.path_lower_bound` proves the cut argument by induction on
   path length, directly over the executable vectors. At a settled predecessor
   it combines its shortest distance, the relaxed frontier, and the minimum
   bound. At an open predecessor it uses induction and nonnegative weights.
3. `StateInvariant.certifies_minimum` combines that lower bound with the
   selected entry's path witness.
4. `StateInvariant.relax_selected` proves all invariant conjuncts after the
   `mark`/`relax` update. Existing settled entries are preserved;
   decreased labels retain witnesses; the new source edge relaxation and the
   previous frontier bounds establish the new frontier.
5. `StateInvariant.advance` includes both scan outcomes. `StateInvariant.iterate`
   lifts it through the recursion, and `solve.invariant` starts from the
   checked initialization.
6. `solve.exhausts_finite_frontier` supplies the consequence of termination
   after `count` iterations. Every finite final
   label is settled and hence shortest. An open reachable vertex would have
   every natural number as a lower bound on its path cost, contradicting the
   bound `succ(cost)`; this establishes unreachability.
7. `StateInvariant.finished_value` uses uniqueness of shortest costs for the
   converse finite-value implication. `solve.correct` assembles both iff claims.

No kernel rule, axiom, `sorry`, or trusted solver was added. The proof covers
every natural size. The six-vertex and zero-weight examples remain as
executable regressions.

## Formalization

The formal representation permits matrix padding beyond the vertex domain,
so it is slightly more general than the square-matrix presentation above. Its
cut induction works directly with vector entries, and the terminal
contradiction uses the bound `succ(cost)` instead of choosing a first crossing
vertex. These are two forms of the same nonnegative path argument.
