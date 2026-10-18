// The Set Theory Game: worlds and levels, each a checked Grace17 theorem.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A level is a theorem with a hole. The page shows `statement` with the
// `starter` proof; the player edits the proof until the check passes with no
// sorry. `solution` is one proof that passes; the tests check both.
// Text fields are HTML fragments; code uses <code>.

// The first tactic word of each proof line, for the per-level switch-off list.
export function forbiddenTacticUsed(level, proof) {
  const banned = new Set(level.forbid ?? []);
  if (!banned.size) return undefined;
  for (const line of proof.split("\n")) {
    const word = /^\s*(?:\.\s*)?([A-Za-z_?]+)/.exec(line)?.[1];
    if (word && banned.has(word)) return word;
    // A dotted entry names a library theorem; it is switched off wherever
    // it appears, so that a by-hand level cannot be closed by citing it.
    for (const token of line.match(/[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+/g) ?? []) {
      if (banned.has(token)) return token;
    }
  }
  return undefined;
}

export function levelSource(world, level, proof) {
  const imports = (level.imports ?? world.imports).map(name => `import ${name}`).join("\n");
  const preamble = level.preamble ? `\n${level.preamble.trimEnd()}\n` : "";
  const body = proof.trimEnd().split("\n").map(line => line ? `  ${line}` : line).join("\n");
  return `module Game.${world.id}.${level.id}\n${imports}\n${preamble}\n${level.statement.trimEnd()}\nproof\n${body}\n`;
}

export const worlds = [
  {
    id: "FiniteSets",
    title: "Finite sets world",
    subtitle: "Build small sets, combine them, count them.",
    imports: ["Grace.Cumulus.Cardinal"],
    intro: `<p>A set is written between braces: <code>{1, 2, 3}</code>. Its members are the numbers 1, 2, and 3, which are themselves sets, since in Grace17 everything is. The order and repetition of members do not matter; only membership does.</p>
<p>Statements about specific finite sets are computations. The tactic <code>decide</code> evaluates such a statement and, when it is true, writes a proof from the membership lemmas of the library; the kernel checks every step of that proof. The first levels use it. After that it is switched off, and you write the same kind of proof yourself from the lemmas that define union, intersection, difference, and the powerset.</p>`,
    levels: [
      {
        id: "Member",
        title: "Is it in?",
        text: `<p>The first question about any set is membership. Replace the <code>sorry</code> with <code>decide</code> and press Check.</p>`,
        statement: `theorem two_is_in
  shows 2 ∈ {1, 2, 3}`,
        starter: `sorry`,
        solution: `decide`,
        hints: ["<code>decide</code>."],
      },
      {
        id: "NotMember",
        title: "Is it out?",
        text: `<p><code>x ∉ A</code> abbreviates <code>¬(x ∈ A)</code>. A false membership is refuted the same way it would be proved: by looking at every member.</p>`,
        statement: `theorem four_is_out
  shows 4 ∉ {1, 2, 3}`,
        starter: `sorry`,
        solution: `decide`,
        hints: ["<code>decide</code> handles negated membership too."],
      },
      {
        id: "Union",
        title: "Union",
        text: `<p><code>A ∪ B</code> collects the members of both. The statement here is fixed, but the Workbench button in the toolbar opens this level as an editable file: change the <code>3</code> on the right to a <code>4</code> there and see what <code>decide</code> says about a false statement. It reports that the statement is false rather than leaving it open.</p>`,
        statement: `theorem union_of_two
  shows {1, 2} ∪ {2, 3} = {1, 2, 3}`,
        starter: `sorry`,
        solution: `decide`,
        hints: ["<code>decide</code>."],
      },
      {
        id: "UnionByHand",
        title: "Union, by hand",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p>From here on <code>decide</code> is switched off. What it writes is an ordinary proof, and this level is one. <code>{1, 2, 3}</code> is built as <code>{1} ∪ {2, 3}</code>, so <code>2 ∈ {1, 2, 3}</code> follows from <code>2 ∈ {2, 3}</code> by the lemma <code>union2.right</code>.</p>
<p>A <code>have</code> records a fact under a name, here proved in place after <code>:=</code>. <code>exact</code> finishes the goal with a lemma applied to its premises: <code>with</code> supplies them, and the lemma's parameters are read off the goal.</p>`,
        statement: `theorem two_is_in_by_hand
  shows 2 ∈ {1, 2, 3}`,
        starter: `have inner : 2 ∈ {2, 3} := pair.left at 2, 3
sorry`,
        solution: `have inner : 2 ∈ {2, 3} := pair.left at 2, 3
exact union2.right with inner`,
        hints: ["<code>pair.left at 2, 3</code> proves <code>2 ∈ {2, 3}</code>.", "<code>exact union2.right with inner</code> lifts it into the union; the sets are inferred from the goal."],
      },
      {
        id: "IntersectionByHand",
        title: "Intersection, by hand",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p><code>A ∩ B</code> is defined as <code>{ x ∈ A | x ∈ B }</code>, and its membership lemma <code>intersection.membership</code> says <code>x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B)</code>. Applying the <code>.backward</code> direction turns the goal into the conjunction, and <code>constructor</code> splits a conjunction into two goals, one per bullet.</p>`,
        statement: `theorem in_both
  shows 2 ∈ {1, 2} ∩ {2, 3}`,
        starter: `apply intersection.membership.backward
constructor
. sorry
. sorry`,
        solution: `apply intersection.membership.backward
constructor
. exact pair.right at 1, 2
. exact pair.left at 2, 3`,
        hints: ["The first goal is <code>2 ∈ {1, 2}</code>: <code>exact pair.right at 1, 2</code>.", "The second is <code>2 ∈ {2, 3}</code>: <code>exact pair.left at 2, 3</code>."],
      },
      {
        id: "DifferenceByHand",
        title: "Difference, by hand",
        forbid: ["decide", "typecheck"],
        text: `<p><code>A ∖ B</code> keeps the members of <code>A</code> that are not in <code>B</code>; type the symbol as <code>\\setminus</code>. The second half of <code>difference.membership</code> is a negation, so after <code>intro h</code> you hold <code>h : 1 ∈ {2}</code> and must reach <code>⊥</code>. The singleton lemma turns <code>h</code> into <code>1 = 2</code>, and <code>simp</code> with the two Peano facts refutes that.</p>`,
        statement: `theorem one_remains
  shows 1 ∈ {1, 2} ∖ {2}`,
        starter: `apply difference.membership.backward
constructor
. sorry
. intro h
  have e := singleton.membership.forward with h
  sorry`,
        solution: `apply difference.membership.backward
constructor
. exact pair.left at 1, 2
. intro h
  have e := singleton.membership.forward with h
  have distinct : 1 ≠ 2 by simp [Naturals.disjoint.zero.succ, Naturals.injective.succ]
  exact distinct with e`,
        hints: ["The first goal is <code>exact pair.left at 1, 2</code>.", "State <code>have distinct : 1 ≠ 2 by simp [Naturals.disjoint.zero.succ, Naturals.injective.succ]</code>.", "<code>exact distinct with e</code> applies the inequality to <code>e : 1 = 2</code> and yields <code>⊥</code>."],
      },
      {
        id: "Empty",
        title: "Nothing is in the empty set",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p><code>∅</code> has no members at all. The axiom <code>set.empty</code> says <code>¬(x ∈ ∅)</code> for every <code>x</code>; applied to a membership it yields <code>⊥</code>, which is exactly what a negated goal asks for after <code>intro</code>.</p>`,
        statement: `theorem nothing_in_empty
  shows 3 ∉ ∅`,
        starter: `intro h
sorry`,
        solution: `intro h
exact set.empty with h`,
        hints: ["<code>exact set.empty with h</code>."],
      },
      {
        id: "SubsetByHand",
        title: "A subset, by hand",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p><code>A ⊆ B</code> means “every member of A is a member of B”, and <code>intros x hx</code> introduces that member directly: <code>x</code> is arbitrary and <code>hx : x ∈ {2}</code> is all you know about it. <code>singleton.membership</code> tells you <code>x = 2</code>; <code>rw e</code> rewrites the goal with that equation, and a pair lemma finishes.</p>`,
        statement: `theorem singleton_inside
  shows {2} ⊆ {1, 2}`,
        starter: `intros x hx
sorry`,
        solution: `intros x hx
have e := singleton.membership.forward with hx
rw e
exact pair.right at 1, 2`,
        hints: ["<code>have e := singleton.membership.forward with hx</code> gives <code>x = 2</code>.", "After <code>rw e</code> the goal is <code>2 ∈ {1, 2}</code>: <code>exact pair.right at 1, 2</code>."],
      },
      {
        id: "OrderByHand",
        title: "Order does not matter, by hand",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p>Two sets with the same members are equal. <code>Subset.antisymmetric</code> reduces the equation to two inclusions, and each inclusion is a case analysis: a member of a pair is the first element or the second. <code>pair.membership</code> states that as an equivalence, <code>cases</code> splits the disjunction, and each case is one rewrite away from a pair lemma.</p>`,
        statement: `theorem pair_commutes
  shows {1, 2} = {2, 1}`,
        starter: `apply Subset.antisymmetric
. intros x hx
  have c := pair.membership.forward with hx
  cases c with e1 | e2
  . rw e1
    sorry
  . rw e2
    sorry
. intros x hx
  have c := pair.membership.forward with hx
  cases c with e1 | e2
  . rw e1
    sorry
  . rw e2
    sorry`,
        solution: `apply Subset.antisymmetric
. intros x hx
  have c := pair.membership.forward with hx
  cases c with e1 | e2
  . rw e1
    exact pair.right at 2, 1
  . rw e2
    exact pair.left at 2, 1
. intros x hx
  have c := pair.membership.forward with hx
  cases c with e1 | e2
  . rw e1
    exact pair.right at 1, 2
  . rw e2
    exact pair.left at 1, 2`,
        hints: ["In the first inclusion, the case <code>x = 1</code> needs <code>1 ∈ {2, 1}</code>: <code>exact pair.right at 2, 1</code>.", "Each hole is one <code>pair.left</code> or <code>pair.right</code>; read the goal to see which."],
      },
      {
        id: "Count",
        title: "Counting",
        text: `<p><code>cardinality(A)</code> is the number of members of a finite set. Here <code>decide</code> is allowed again: behind the scenes its proof inserts the members one at a time, checking that each is new, with <code>cardinality.insert</code>.</p>`,
        statement: `theorem three_members
  shows cardinality({1, 2} ∪ {2, 3}) = 3`,
        starter: `sorry`,
        solution: `decide`,
        hints: ["<code>decide</code>."],
      },
      {
        id: "PowersetByHand",
        title: "Into the powerset, by hand",
        forbid: ["decide", "typecheck", "settle", "simp"],
        text: `<p><code>𝒫(A)</code>, the powerset, is the set of all subsets of <code>A</code>; type it as <code>\\powerset</code>. <code>powerset.membership_iff</code> says <code>S ∈ 𝒫(A) ↔ S ⊆ A</code>, so the level is the previous subset proof behind one more <code>apply</code>.</p>`,
        statement: `theorem subset_in_powerset
  shows {1} ∈ 𝒫({1, 2})`,
        starter: `apply powerset.membership_iff.backward
sorry`,
        solution: `apply powerset.membership_iff.backward
intros x hx
have e := singleton.membership.forward with hx
rw e
exact pair.left at 1, 2`,
        hints: ["After the <code>apply</code> the goal is <code>{1} ⊆ {1, 2}</code>.", "<code>intros x hx</code>, the singleton lemma, <code>rw e</code>, then <code>pair.left at 1, 2</code>."],
      },
    ],
  },
  {
    id: "Logic",
    title: "Logic world",
    subtitle: "The connectives, one tactic each.",
    imports: ["Grace.Cumulus.Set"],
    intro: `<p>Grace17 proofs are natural deduction. Each connective has a tactic that takes it apart when it is a hypothesis and a tactic that builds it when it is the goal: <code>obtain ⟨ha, hb⟩</code> and <code>constructor</code> for <code>∧</code>, <code>cases</code> and <code>left</code> or <code>right</code> for <code>∨</code>, <code>intro</code> for <code>→</code> and <code>¬</code>, <code>obtain ⟨x, hx⟩</code> and <code>witness</code> for <code>∃</code>. Nothing else is needed; the kernel checks every step against these rules.</p>
<p>The statements here are about membership in arbitrary sets, which is the only atomic relation there is, so they are honest first-order logic rather than a sandbox. The goal pane on the right shows the hypotheses above the line and the goal below it; watch both change after every tactic.</p>`,
    levels: [
      {
        id: "And",
        title: "And",
        text: `<p>A hypothesis <code>h : P ∧ Q</code> comes apart with <code>obtain ⟨ha, hb⟩ := h</code>, which names both halves. A goal <code>P ∧ Q</code> splits with <code>constructor</code> into two goals, each closed under its own bullet <code>.</code> with <code>exact</code>.</p>`,
        statement: `theorem and_swap (x A B : Set)
  requires h : x ∈ A ∧ x ∈ B
  shows x ∈ B ∧ x ∈ A`,
        starter: `obtain ⟨ha, hb⟩ := h
constructor
. sorry
. sorry`,
        solution: `obtain ⟨ha, hb⟩ := h
constructor
. exact hb
. exact ha`,
        hints: ["The first goal is <code>x ∈ B</code>, which is <code>hb</code>.", "<code>. exact hb</code> then <code>. exact ha</code>."],
      },
      {
        id: "Or",
        title: "Or",
        text: `<p>A disjunction hypothesis is a case split: <code>cases h with ha | hb</code> opens one goal per side, with the chosen side as a hypothesis. A disjunction goal is proved by picking a side with <code>left</code> or <code>right</code> and proving it.</p>`,
        statement: `theorem or_swap (x A B : Set)
  requires h : x ∈ A ∨ x ∈ B
  shows x ∈ B ∨ x ∈ A`,
        starter: `cases h with ha | hb
. sorry
. sorry`,
        solution: `cases h with ha | hb
. right
  exact ha
. left
  exact hb`,
        hints: ["In the first case you hold <code>ha : x ∈ A</code>, which is the right side of the goal: <code>right</code>, then <code>exact ha</code>.", "In the second case: <code>left</code>, then <code>exact hb</code>."],
      },
      {
        id: "Implies",
        title: "Implication",
        text: `<p>To prove <code>P → Q</code>, assume <code>P</code> with <code>intro ha</code> and prove <code>Q</code>. To use an implication, feed it its premise with <code>with</code>: <code>hab with ha</code> is a proof of <code>x ∈ B</code>. Record intermediate facts with <code>have</code>.</p>`,
        statement: `theorem implication_chain (x A B C : Set)
  requires hab : x ∈ A → x ∈ B
  requires hbc : x ∈ B → x ∈ C
  shows x ∈ A → x ∈ C`,
        starter: `intro ha
sorry`,
        solution: `intro ha
have hb := hab with ha
exact hbc with hb`,
        hints: ["<code>have hb := hab with ha</code> records <code>x ∈ B</code>.", "<code>exact hbc with hb</code>."],
      },
      {
        id: "Not",
        title: "Not",
        text: `<p><code>¬P</code> is <code>P → ⊥</code>, an implication into the absurd, so <code>intro</code> assumes <code>P</code> and leaves <code>⊥</code> to show. A negated hypothesis applied to the thing it denies produces exactly that. The two halves of a conjunction are also reachable as <code>h.left</code> and <code>h.right</code>.</p>`,
        statement: `theorem not_both (x A B : Set)
  requires h : x ∉ B
  shows ¬(x ∈ A ∧ x ∈ B)`,
        starter: `intro both
sorry`,
        solution: `intro both
exact h with both.right`,
        hints: ["<code>both.right</code> is <code>x ∈ B</code>, which <code>h</code> denies.", "<code>exact h with both.right</code>."],
      },
      {
        id: "Exists",
        title: "There exists",
        text: `<p>An existential hypothesis gives a witness and a fact about it: <code>obtain ⟨x, hx⟩ := h</code>. The goal <code>A ≠ ∅</code> is a negation, so assume <code>A = ∅</code> and rewrite the fact about <code>x</code> with it; <code>set.empty</code>, the axiom that <code>∅</code> has no members, finishes.</p>`,
        statement: `theorem exists_member (A : Set)
  requires h : ∃ x, x ∈ A
  shows A ≠ ∅`,
        starter: `obtain ⟨x, hx⟩ := h
intro empty
sorry`,
        solution: `obtain ⟨x, hx⟩ := h
intro empty
rw empty at hx
exact set.empty with hx`,
        hints: ["<code>rw empty at hx</code> turns <code>hx</code> into <code>x ∈ ∅</code>.", "<code>exact set.empty with hx</code>."],
      },
      {
        id: "ExcludedMiddle",
        title: "Excluded middle",
        text: `<p>Grace17's logic is classical: every statement is true or false. <code>tauto</code> proves any propositional tautology, and <code>by_contra h</code> assumes the negation of the goal. The by-hand proof below is the classical derivation of <code>P ∨ ¬P</code> from double negation, in six lines; the kernel checks either.</p>`,
        statement: `theorem excluded_middle (x A : Set)
  shows x ∈ A ∨ x ∉ A`,
        starter: `sorry`,
        solution: `tauto`,
        hints: ["<code>tauto</code>.", "By hand: <code>by_contra neither</code>, <code>apply neither</code>, <code>right</code>, <code>intro hx</code>, <code>apply neither</code>, <code>left</code>, <code>exact hx</code>."],
      },
    ],
  },
  {
    id: "Membership",
    title: "Membership world",
    subtitle: "Everything is a set, and every question is about ∈.",
    imports: ["Grace.Cumulus.Set"],
    intro: `<p>In Grace17 every mathematical object is a set. There is one universe, and the only primitive relation is membership, <code>x ∈ A</code>. Equality of sets is decided by their members: <code>A = B</code> exactly when the two sets have the same elements. That one principle, extensionality, is the engine of this world.</p>
<p>From here on the sets are arbitrary, so computation gives way to the proofs of Logic world, now about sets. <code>intros x hx</code> takes an arbitrary member of a set, a library fact is applied to what it needs with <code>with</code>, <code>ext y</code> reduces an equation between sets to a membership question about an arbitrary <code>y</code>, and <code>simp</code> settles the membership logic of <code>∅</code>, <code>∪</code>, <code>∩</code>, <code>∖</code>, <code>{x}</code>, and <code>𝒫</code> from the hypotheses in play. The proofs read like the mathematics.</p>`,
    levels: [
      {
        id: "SubsetSelf",
        title: "A set is a subset of itself",
        text: `<p><code>A ⊆ B</code> abbreviates <code>Subset(A, B)</code>, defined as “every member of A is a member of B”. <code>intros x hx</code> sees through that definition: it names an arbitrary member <code>x</code> and the hypothesis <code>hx : x ∈ A</code>, and leaves <code>x ∈ A</code> to show. <code>exact hx</code> closes a goal with a hypothesis that is exactly the goal.</p>`,
        statement: `theorem subset_self (A : Set)
  shows A ⊆ A`,
        starter: `sorry`,
        solution: `intros x hx
exact hx`,
        hints: ["Start with <code>intros x hx</code> and watch the goal change.", "The hypothesis <code>hx : x ∈ A</code> is the goal."],
      },
      {
        id: "SubsetTransitive",
        title: "Subsets chain",
        text: `<p>A subset hypothesis is a fact about every member, and it applies to one with <code>with</code>: <code>hab with x, hx</code> instantiates it at <code>x</code> and feeds it the membership proof <code>hx</code>, giving <code>x ∈ B</code>. Record that under a name with <code>have</code>, then apply the second hypothesis the same way.</p>`,
        statement: `theorem subset_transitive (A B C : Set)
  requires hab : A ⊆ B
  requires hbc : B ⊆ C
  shows A ⊆ C`,
        starter: `intros x hx
sorry`,
        solution: `intros x hx
have hb := hab with x, hx
exact hbc with x, hb`,
        hints: ["<code>have hb := hab with x, hx</code> records that <code>x ∈ B</code>.", "Now <code>hbc with x, hb</code> is exactly the goal."],
      },
      {
        id: "InjectiveCancel",
        title: "Injective functions cancel",
        text: `<p><code>InjectiveBetween(f, A, B)</code> unfolds to the function property together with "two points sent to the same value are equal", stated on the graph: <code>relates(f, x, z) → relates(f, y, z) → x = y</code>. To use it on <code>f(x) = f(y)</code>, put both pairs <code>(x ↦ f(x))</code> and <code>(y ↦ f(y))</code> in the graph with <code>FunctionBetween.relates_apply</code>, rewrite the first with <code>same</code>, and apply the cancellation law with every argument it asks for.</p>`,
        statement: `theorem injective_cancel (A B x y : Set) (f : A → B)
  requires injective : InjectiveBetween(f, A, B)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires same : f(x) = f(y)
  shows x = y`,
        starter: `obtain ⟨function, cancel⟩ := injective
have mapsX := FunctionBetween.relates_apply with function, hx
have mapsY := FunctionBetween.relates_apply with function, hy
sorry`,
        solution: `obtain ⟨function, cancel⟩ := injective
have mapsX := FunctionBetween.relates_apply with function, hx
have mapsY := FunctionBetween.relates_apply with function, hy
have valueIn : f(y) ∈ B := FunctionBetween.apply_closed with *
rw same at mapsX
exact cancel with x, hx, y, hy, f(y), valueIn, mapsX, mapsY`,
        hints: ["<code>rw same at mapsX</code> turns it into <code>relates(f, x, f(y))</code>.", "The law also needs <code>f(y) ∈ B</code>: <code>have valueIn : f(y) ∈ B := FunctionBetween.apply_closed with *</code>.", "<code>exact cancel with x, hx, y, hy, f(y), valueIn, mapsX, mapsY</code>."],
      },
      {
        id: "Ext",
        title: "Intersection commutes",
        text: `<p>To prove two sets equal, show that an arbitrary <code>y</code> belongs to one exactly when it belongs to the other. <code>ext y</code> makes that the goal, <code>y ∈ A ∩ B ↔ y ∈ B ∩ A</code>, and <code>simp</code> settles it from the membership lemma of <code>∩</code>: both sides say <code>y ∈ A ∧ y ∈ B</code> in some order.</p>`,
        statement: `theorem meet_commutes (A B : Set)
  shows A ∩ B = B ∩ A`,
        starter: `ext y
sorry`,
        solution: `ext y
simp`,
        hints: ["After <code>ext y</code> the goal is an equivalence between two memberships.", "<code>simp</code> knows the membership lemmas of <code>∩</code>."],
      },
      {
        id: "EmptyBelow",
        title: "The empty set is below everything",
        text: `<p><code>∅</code> has no members, which the axiom <code>set.empty</code> states as <code>¬(x ∈ ∅)</code> for every <code>x</code>. So a member of <code>∅</code> is a contradiction, and from a contradiction anything follows. <code>simp</code> sees this on its own; by hand it is <code>intros x hx</code>, <code>exfalso</code>, and <code>exact set.empty with hx</code>.</p>`,
        statement: `theorem empty_below (A : Set)
  shows ∅ ⊆ A`,
        starter: `sorry`,
        solution: `simp`,
        hints: ["<code>simp</code>.", "Or by hand: after <code>intros x hx</code> the hypothesis <code>hx : x ∈ ∅</code> is impossible; <code>exfalso</code>, then <code>exact set.empty with hx</code>."],
      },
      {
        id: "UnionLeft",
        title: "Below a union",
        text: `<p><code>A ∪ B</code> is the union of the pair <code>{A, B}</code>, and <code>simp</code> proves that <code>A</code> sits below it from the membership lemma of <code>∪</code>. Cumulus also proved it under the name <code>union2.subset_left</code>: finding and applying the right theorem is most of real formal work, and the Workbench search (⌘⇧F) finds it by name or by statement.</p>`,
        statement: `theorem below_union (A B : Set)
  shows A ⊆ A ∪ B`,
        starter: `sorry`,
        solution: `simp`,
        hints: ["<code>simp</code>.", "Or search for <code>subset_left</code> and write <code>exact union2.subset_left at A, B</code>."],
      },
      {
        id: "IntersectionBelow",
        title: "An intersection is below its parts",
        text: `<p><code>A ∩ B</code> is the comprehension <code>{ x ∈ A | x ∈ B }</code>. Its membership rule is <code>intersection.membership</code>; this time prove the subset directly from it rather than with <code>simp</code>. The rule is an equivalence, so use its <code>.forward</code> direction, and take the conjunction apart with <code>obtain ⟨ha, hb⟩</code>.</p>`,
        forbid: ["simp", "settle"],
        statement: `theorem meet_below (A B : Set)
  shows A ∩ B ⊆ A`,
        starter: `intros x hx
sorry`,
        solution: `intros x hx
obtain ⟨ha, hb⟩ := intersection.membership.forward with hx
exact ha`,
        hints: ["<code>intersection.membership.forward with hx</code> gives <code>x ∈ A ∧ x ∈ B</code>.", "<code>obtain ⟨ha, hb⟩ := …</code> names both halves at once."],
      },
      {
        id: "DifferenceMono",
        title: "Difference respects inclusion",
        text: `<p>Removing the same set from a smaller set gives a smaller set. <code>simp</code> proves it from the hypothesis <code>h</code> and the membership lemma of <code>∖</code>. By hand the proof is four lines: introduce <code>x</code>, split <code>hx</code> with <code>obtain ⟨ha, hc⟩</code>, move <code>x</code> into <code>B</code> with <code>h</code>, and rebuild the membership with <code>difference.membership.backward with ⟨hb, hc⟩</code>.</p>`,
        statement: `theorem difference_mono (A B C : Set)
  requires h : A ⊆ B
  shows A ∖ C ⊆ B ∖ C`,
        starter: `sorry`,
        solution: `simp`,
        hints: ["<code>simp</code>.", "By hand: <code>intros x hx</code>, <code>obtain ⟨ha, hc⟩ := difference.membership.forward with hx</code>, <code>have hb := h with x, ha</code>, <code>exact difference.membership.backward with ⟨hb, hc⟩</code>."],
      },
      {
        id: "Powerset",
        title: "Into the powerset",
        text: `<p><code>𝒫(B)</code> is the set of all subsets of <code>B</code>, and <code>powerset.membership_iff</code> says <code>A ∈ 𝒫(B) ↔ A ⊆ B</code>. Equivalences have a <code>.backward</code> direction too.</p>`,
        statement: `theorem in_powerset (A B : Set)
  requires h : A ⊆ B
  shows A ∈ 𝒫(B)`,
        starter: `sorry`,
        solution: `exact powerset.membership_iff.backward with h`,
        hints: ["The equivalence is <code>powerset.membership_iff (A B : Set)</code>.", "Use its <code>.backward</code> direction with <code>h</code>."],
      },
      {
        id: "Singleton",
        title: "A singleton inside a set",
        text: `<p><code>{x}</code> has exactly one member. <code>singleton.membership</code> says <code>y ∈ {x} ↔ y = x</code>. Once you know <code>y = x</code>, <code>rwa eq</code> rewrites the goal with it and closes it with the hypothesis <code>h</code> in one move.</p>`,
        statement: `theorem singleton_below (x A : Set)
  requires h : x ∈ A
  shows {x} ⊆ A`,
        starter: `intros y hy
sorry`,
        solution: `intros y hy
have eq := singleton.membership.forward with hy
rwa eq`,
        hints: ["<code>singleton.membership.forward with hy</code> gives <code>y = x</code>.", "<code>rwa eq</code> turns the goal <code>y ∈ A</code> into <code>x ∈ A</code> and finishes with <code>h</code>."],
      },
    ],
  },
  {
    id: "Foundation",
    title: "Paradox world",
    subtitle: "Why there is no set of all sets.",
    imports: ["Grace.Cumulus.Set"],
    intro: `<p>Naive set theory asked for a set of everything and got Russell's paradox. The axioms of ZF avoid it: comprehension only carves subsets out of sets you already have, and the axiom of foundation says every nonempty set has a member disjoint from it, which rules out <code>x ∈ x</code> and all longer membership cycles. The collection of all sets is still there, as a <em>class</em>, and in Grace17 you can write it: <code>Universe</code>.</p>
<p>These levels are the classical arguments, each a few lines. They are also where the cumulative hierarchy begins: every set is built from earlier sets, and nothing is built from itself.</p>`,
    levels: [
      {
        id: "NotSelf",
        title: "No set is a member of itself",
        text: `<p>Cumulus proves this twice, once from the axiom of foundation and once by <code>induction x using membership</code>, the ∈-induction principle derived from it. The library theorem is <code>membership.irreflexive</code>; hover it in the Workbench to read both.</p>`,
        statement: `theorem no_self_membership (x : Set)
  shows x ∉ x`,
        starter: `sorry`,
        solution: `exact membership.irreflexive at x`,
        hints: ["<code>exact membership.irreflexive at x</code>."],
      },
      {
        id: "NotSelfByHand",
        title: "No set is a member of itself, by hand",
        forbid: ["simp", "settle", "tauto"],
        text: `<p>The axiom <code>set.foundation</code> says a nonempty set <code>S</code> has a member <code>m</code> with <code>∀ z ∈ m, z ∉ S</code>. Apply it to <code>{x}</code>: the member must be <code>x</code> itself, and then <code>x ∈ x</code> would put <code>x</code> inside <code>{x}</code>, which the axiom forbids. <code>rw ← eq at hxx</code> rewrites <code>x</code> to <code>m</code> inside the hypothesis.</p>`,
        statement: `theorem no_self_membership_by_hand (x : Set)
  shows x ∉ x`,
        starter: `intro hxx
have nonempty := singleton.ne_empty at x
obtain ⟨m, hm, minimal⟩ := set.foundation with nonempty
have eq := singleton.membership.forward with hm
sorry`,
        solution: `intro hxx
have nonempty := singleton.ne_empty at x
obtain ⟨m, hm, minimal⟩ := set.foundation with nonempty
have eq := singleton.membership.forward with hm
rw ← eq at hxx
have outside := minimal with m, hxx
exact outside with hm`,
        hints: ["<code>rw ← eq at hxx</code> turns <code>hxx</code> into <code>m ∈ m</code>.", "<code>minimal with m, hxx</code> says <code>m ∉ {x}</code>, against <code>hm</code>.", "<code>have outside := minimal with m, hxx</code>, then <code>exact outside with hm</code>."],
      },
      {
        id: "NoUniversalSet",
        title: "There is no set of all sets",
        text: `<p>A set containing every set would contain itself. Take the existential apart, specialize the universal hypothesis to <code>U</code> itself, and the previous level finishes.</p>`,
        statement: `theorem no_universal_set
  shows ¬(∃ U, ∀ x, x ∈ U)`,
        starter: `intro h
obtain ⟨U, hU⟩ := h
sorry`,
        solution: `intro h
obtain ⟨U, hU⟩ := h
have self := hU with U
exact membership.irreflexive with self`,
        hints: ["<code>hU with U</code> is <code>U ∈ U</code>.", "<code>exact membership.irreflexive with self</code>."],
      },
      {
        id: "Russell",
        title: "Russell's paradox",
        text: `<p>Russell's own argument needs no foundation axiom. For any set <code>U</code>, the subset of members of <code>U</code> that are not members of themselves cannot belong to <code>U</code>: if it did, it would be a member of itself exactly when it is not. The definition and its membership lemma sit above the theorem; <code>tauto</code> supplies the case split, and each case is one application of the lemma.</p>`,
        preamble: `def russellSet (U : Set) : Set := { x ∈ U | x ∉ x }

theorem russellSet.membership (x U : Set)
  shows x ∈ russellSet(U) ↔ x ∈ U ∧ x ∉ x
proof
  simp [russellSet]`,
        statement: `theorem russell (U : Set)
  shows russellSet(U) ∉ U`,
        starter: `intro h
have split : russellSet(U) ∈ russellSet(U) ∨ russellSet(U) ∉ russellSet(U) by tauto
cases split with inside | outside
. sorry
. sorry`,
        solution: `intro h
have split : russellSet(U) ∈ russellSet(U) ∨ russellSet(U) ∉ russellSet(U) by tauto
cases split with inside | outside
. have facts := russellSet.membership.forward with inside
  exact facts.right with inside
. apply outside
  apply russellSet.membership.backward
  exact ⟨h, outside⟩`,
        hints: ["Inside: <code>russellSet.membership.forward with inside</code> says the set is in <code>U</code> and not in itself; its <code>.right</code> contradicts <code>inside</code>.", "Outside: <code>apply outside</code> asks you to show it is in itself; <code>apply russellSet.membership.backward</code> asks for <code>h</code> and <code>outside</code> together, as <code>⟨h, outside⟩</code>."],
      },
      {
        id: "Universe",
        title: "The class of all sets",
        text: `<p>What ZF cannot make a set, Grace17 lets you name as a class. <code>Universe</code> is declared as <code>class Universe (x : Set) := { x | x = x }</code>, and membership in it is proved by unfolding the class with <code>simp</code>. The previous level shows why it can never be a set.</p>`,
        statement: `theorem everything_in_universe (A : Set)
  shows A ∈ Universe`,
        starter: `sorry`,
        solution: `simp [Universe]`,
        hints: ["<code>simp [Universe]</code>."],
      },
      {
        id: "Pairs",
        title: "Ordered pairs",
        text: `<p>An ordered pair is a set too: <code>(a ↦ b)</code> is Kuratowski's <code>{{a}, {a, b}}</code>. The whole point of the encoding is that it remembers which came first, and <code>orderedPair.injective</code> proves that from the pair lemmas. Type the arrow as <code>\\mapsto</code>.</p>`,
        statement: `theorem pairs_injective (a b c d : Set)
  requires h : (a ↦ b) = (c ↦ d)
  shows a = c ∧ b = d`,
        starter: `sorry`,
        solution: `exact orderedPair.injective with h`,
        hints: ["<code>exact orderedPair.injective with h</code>."],
      },
      {
        id: "SingletonNotSelf",
        title: "A set is not its own singleton",
        text: `<p>If <code>{x} = x</code>, then since <code>x ∈ {x}</code> we would have <code>x ∈ x</code>. <code>rw eq at self</code> performs the substitution inside the hypothesis.</p>`,
        statement: `theorem singleton_not_self (x : Set)
  shows {x} ≠ x`,
        starter: `intro eq
have self := singleton.self at x
sorry`,
        solution: `intro eq
have self := singleton.self at x
rw eq at self
exact membership.irreflexive with self`,
        hints: ["<code>rw eq at self</code> turns <code>x ∈ {x}</code> into <code>x ∈ x</code>.", "<code>exact membership.irreflexive with self</code>."],
      },
    ],
  },
  {
    id: "Computation",
    title: "Computation world",
    subtitle: "Definitions run. Ground facts are checked by running them.",
    imports: ["Grace.Core.Nat"],
    intro: `<p>Natural numbers are the von Neumann numerals: <code>0 = ∅</code>, <code>1 = {0}</code>, <code>2 = {0, 1}</code>, and so on. They form the datatype <code>Nat</code>, and functions on them are defined by recursion. Such definitions are executable: the kernel evaluates them, and the tactic <code>compute</code> proves any closed equation that evaluation settles. No arithmetic axioms are assumed; <code>2 + 2 = 4</code> is a theorem about sets.</p>`,
    levels: [
      {
        id: "TwoPlusTwo",
        title: "Two plus two",
        text: `<p><code>add</code> is defined by recursion on its first argument, and <code>+</code> is notation for it. The goal is closed, so let the kernel compute.</p>`,
        statement: `theorem two_plus_two
  shows 2 + 2 = 4`,
        starter: `sorry`,
        solution: `compute`,
        hints: ["<code>compute</code>."],
      },
      {
        id: "Double",
        title: "Your own function",
        text: `<p>Define a function by recursion, then prove a value of it. The definition is above the theorem; equations are matched in order. <code>double</code> is new, so nothing in the library knows it, and still <code>compute</code> runs it.</p>`,
        preamble: `def double (n : Nat) → Nat
  | zero => 0
  | succ(k) => succ(succ(double(k)))`,
        statement: `theorem double_five
  shows double(5) = 10`,
        starter: `sorry`,
        solution: `compute`,
        hints: ["Evaluation unfolds <code>double</code> five times.", "<code>compute</code>."],
      },
      {
        id: "Factorial",
        title: "Factorial",
        text: `<p><code>factorial</code> is in the Core library, defined with <code>mul</code>. Evaluation of <code>factorial(5)</code> builds the numeral 120 as a set of 120 sets, and the proof is still one word.</p>`,
        statement: `theorem factorial_five
  shows 5! = 120`,
        starter: `sorry`,
        solution: `compute`,
        hints: ["<code>compute</code>."],
      },
      {
        id: "AddZero",
        title: "From values to all values",
        text: `<p><code>compute</code> only handles closed terms. A statement about every <code>n</code> needs induction, which follows the two constructors of <code>Nat</code>. In each case, <code>settle with add</code> unfolds the definition of <code>add</code> and closes what is left; in the successor case the induction hypothesis <code>ih</code> is also needed.</p>`,
        statement: `theorem add_zero (n : Nat)
  shows n + 0 = n`,
        starter: `induction n
| zero => sorry
| succ(k) using ih => sorry`,
        solution: `induction n
| zero => settle with add
| succ(k) using ih => settle with add, ih`,
        hints: ["The zero case is a computation: <code>settle with add</code>.", "The successor case unfolds one step and uses <code>ih</code>: <code>settle with add, ih</code>."],
      },
      {
        id: "DoubleIsAdd",
        title: "Double is adding to itself",
        imports: ["Grace.Core.Nat.Algebra"],
        text: `<p>Now relate your function to the library's. The successor case needs the library fact <code>add.succ_right</code>, which moves a successor out of the second argument. Pass it to <code>settle</code> along with the definitions.</p>`,
        preamble: `def double (n : Nat) → Nat
  | zero => 0
  | succ(k) => succ(succ(double(k)))`,
        statement: `theorem double_is_add (n : Nat)
  shows double(n) = n + n`,
        starter: `induction n
| zero => sorry
| succ(k) using ih => sorry`,
        solution: `induction n
| zero => settle with double, add
| succ(k) using ih => settle with double, add, add.succ_right, ih`,
        hints: ["Zero case: <code>settle with double, add</code>.", "Successor case: <code>settle with double, add, add.succ_right, ih</code>."],
      },
    ],
  },
  {
    id: "Functions",
    title: "Function world",
    subtitle: "A function is a set of ordered pairs.",
    imports: ["Grace.Cumulus.Set.Function"],
    intro: `<p>There is no primitive notion of function. <code>f : A → B</code> is notation for <code>FunctionBetween(f, A, B)</code>: <code>f</code> is a set of ordered pairs <code>(x ↦ y)</code> with <code>x ∈ A</code> and <code>y ∈ B</code>, exactly one pair for each <code>x</code>. Application <code>f(x)</code> picks the second component. Everything you know about functions is a theorem about such sets.</p>
<p>The arrow can also appear in a theorem's parameter list, <code>(f : A → B)</code>, where it is a hypothesis without a name; <code>with *</code> lets the elaborator supply it, and <code>synthesize</code> builds function-space facts such as "the composite of two functions is a function" from the declared instances.</p>`,
    levels: [
      {
        id: "Identity",
        title: "The identity function",
        text: `<p><code>identity(A)</code> is <code>{ p ∈ A × A | ∃ x ∈ A, p = (x ↦ x) }</code>. Cumulus proves it is a function from <code>A</code> to <code>A</code>; hover the arrow in the statement to see the predicate it stands for.</p>`,
        statement: `theorem identity_is_function (A : Set)
  shows identity(A) : A → A`,
        starter: `sorry`,
        solution: `exact identity.function at A`,
        hints: ["<code>identity.function at A</code>."],
      },
      {
        id: "ValueInCodomain",
        title: "Values land in the codomain",
        text: `<p><code>FunctionBetween.apply_closed</code> is the theorem behind every "f(x) ∈ B" step in Cumulus. Here <code>f : A → B</code> is a parameter rather than a named hypothesis, so ask for it with <code>with *</code>, which fills every premise it can find.</p>`,
        statement: `theorem value_in_codomain (A B x : Set) (f : A → B)
  requires hx : x ∈ A
  shows f(x) ∈ B`,
        starter: `sorry`,
        solution: `exact FunctionBetween.apply_closed with *`,
        hints: ["<code>exact FunctionBetween.apply_closed with *</code>."],
      },
      {
        id: "TwoSteps",
        title: "Two steps",
        text: `<p>Chain the previous level: first <code>f(x) ∈ B</code>, then <code>g</code> applied to it. State the intermediate fact with <code>have hy : f(x) ∈ B := …</code> so that <code>with *</code> can find it for the second step.</p>`,
        statement: `theorem two_steps (A B C x : Set) (f : A → B) (g : B → C)
  requires hx : x ∈ A
  shows g(f(x)) ∈ C`,
        starter: `have hy : f(x) ∈ B
  sorry
sorry`,
        solution: `have hy : f(x) ∈ B := FunctionBetween.apply_closed with *
exact FunctionBetween.apply_closed with *`,
        hints: ["Both steps are <code>FunctionBetween.apply_closed with *</code>.", "The stated <code>have</code> is what lets the second step find <code>f(x) ∈ B</code>."],
      },
      {
        id: "Compose",
        title: "Composition",
        text: `<p><code>compose(g, f, A, B, C)</code> is the set of pairs <code>(x ↦ g(f(x)))</code>. That it is a function from <code>A</code> to <code>C</code> is an <code>instance</code> in Cumulus, so <code>synthesize</code> assembles the proof from the two arrows in the parameter list. The theorem behind it is <code>compose.function</code>.</p>`,
        statement: `theorem compose_is_function (A B C : Set) (f : A → B) (g : B → C)
  shows compose(g, f, A, B, C) : A → C`,
        starter: `sorry`,
        solution: `synthesize`,
        hints: ["<code>synthesize</code>.", "Or name the theorem: <code>exact compose.function with *</code>."],
      },
      {
        id: "Image",
        title: "Into the image",
        text: `<p><code>functionImage(f, A, B)</code> is the set of values <code>{ f(x) | x ∈ A }</code>, and its membership law is <code>y ∈ functionImage(f, A, B) ↔ y ∈ B ∧ ∃ x ∈ A, y = f(x)</code>. Apply the backward direction, split the conjunction, and supply <code>x</code> as the witness: <code>⟨hx, rfl⟩</code> proves <code>x ∈ A ∧ f(x) = f(x)</code> in one stroke.</p>`,
        statement: `theorem value_in_image (A B x : Set) (f : A → B)
  requires hx : x ∈ A
  shows f(x) ∈ functionImage(f, A, B)`,
        starter: `apply functionImage.membership.backward
constructor
. sorry
. sorry`,
        solution: `apply functionImage.membership.backward
constructor
. exact FunctionBetween.apply_closed with *
. witness x
  exact ⟨hx, rfl⟩`,
        hints: ["The first goal is <code>f(x) ∈ B</code>: <code>exact FunctionBetween.apply_closed with *</code>.", "The second is an existential: <code>witness x</code>, then <code>exact ⟨hx, rfl⟩</code>."],
      },
      {
        id: "IdentityValue",
        title: "The identity does nothing",
        forbid: ["identity.apply"],
        text: `<p>Application is defined from the graph: <code>FunctionBetween.apply_value</code> says that if <code>f</code> is a function and the pair <code>(x ↦ y)</code> is in it, then <code>f(x) = y</code>. For the identity, <code>identity.relates</code> puts <code>(x ↦ x)</code> in the graph whenever <code>x ∈ A</code>. Three facts, one conclusion.</p>`,
        statement: `theorem identity_does_nothing (A x : Set)
  requires hx : x ∈ A
  shows identity(A)(x) = x`,
        starter: `have function := identity.function at A
sorry`,
        solution: `have function := identity.function at A
have mapped := identity.relates with hx
exact FunctionBetween.apply_value with function, hx, mapped`,
        hints: ["<code>have mapped := identity.relates with hx</code> gives <code>relates(identity(A), x, x)</code>.", "<code>exact FunctionBetween.apply_value with function, hx, mapped</code>."],
      },
      {
        id: "Constant",
        title: "A constant function",
        text: `<p><code>constantFunction(A, B, y)</code> sends every member of <code>A</code> to <code>y</code>. It is a function into <code>B</code> as soon as <code>y ∈ B</code>.</p>`,
        statement: `theorem constant_is_function (A B y : Set)
  requires hy : y ∈ B
  shows constantFunction(A, B, y) : A → B`,
        starter: `sorry`,
        solution: `exact constantFunction.function at A, B, y with hy`,
        hints: ["<code>constantFunction.function at A, B, y with hy</code>."],
      },
      {
        id: "Extensionality",
        title: "Functions that agree are equal",
        text: `<p>Two functions on the same domain with the same values are the same set of pairs. <code>FunctionBetween.ext</code> is the function extensionality principle, proved rather than assumed.</p>`,
        statement: `theorem functions_ext (A B : Set) (f : A → B) (g : A → B)
  requires same : ∀ x ∈ A, f(x) = g(x)
  shows f = g`,
        starter: `sorry`,
        solution: `exact FunctionBetween.ext with *`,
        hints: ["<code>exact FunctionBetween.ext with *</code>."],
      },
      {
        id: "ComposeIdentity",
        title: "Composing with the identity",
        text: `<p>Composing <code>f</code> after the identity gives <code>f</code> back, as sets. <code>compose.identity_right</code> is proved by the extensionality of the previous level.</p>`,
        statement: `theorem compose_identity (A B : Set) (f : A → B)
  shows compose(f, identity(A), A, A, B) = f`,
        starter: `sorry`,
        solution: `exact compose.identity_right with *`,
        hints: ["<code>exact compose.identity_right with *</code>."],
      },
    ],
  },
  {
    id: "Algebra",
    title: "Algebra world",
    subtitle: "A group is a set with a function on it.",
    imports: ["Grace.Cumulus.Algebra.Group"],
    intro: `<p>A group is one structure <code>G</code> bundling its carrier, operation, unit, and inverse, read back by the projections <code>G.carrier</code>, <code>G.mul</code>, <code>G.one</code>, and <code>G.inv</code>; <code>Group(G)</code> states the laws. Under that hypothesis the operation is written <code>a * b</code> and the inverse <code>a⁻¹</code>, exactly as in a textbook, and the elements are the members of <code>G.carrier</code>.</p>
<p>The laws have short standard names: <code>mul_assoc</code>, <code>one_mul</code>, <code>mul_one</code>, <code>Group.inv_mul</code>, <code>Group.mul_inv</code>. They are rewrite rules whose side conditions, the carrier memberships, are discharged from the hypotheses, so a proof is the chain of rewrites one would write on paper; <code>group_simp</code> applies the whole set at once.</p>`,
    levels: [
      {
        id: "InverseUnit",
        title: "The inverse of the unit",
        forbid: ["inv_one", "group_simp", "simp"],
        text: `<p>The first lemma of group theory: <code>G.one⁻¹ = G.one</code>. The argument is two facts about the same product: <code>G.one⁻¹ * G.one = G.one</code> because <code>G.one⁻¹</code> is an inverse, and <code>G.one⁻¹ * G.one = G.one⁻¹</code> because the unit is a right identity. The starter records the first; rewrite it with <code>mul_one</code> and the goal follows.</p>`,
        statement: `theorem inverse_of_unit (G : Set)
  requires group : Group(G)
  shows G.one⁻¹ = G.one`,
        starter: `have cancel : G.one⁻¹ * G.one = G.one := Group.inv_mul with *
sorry`,
        solution: `have cancel : G.one⁻¹ * G.one = G.one := Group.inv_mul with *
rwa mul_one at cancel`,
        hints: ["<code>mul_one</code> says <code>a * G.one = a</code>; applied inside <code>cancel</code> it turns the product into <code>G.one⁻¹</code>.", "<code>rwa mul_one at cancel</code> rewrites the recorded equation and closes the goal with it."],
      },
      {
        id: "LeftCancel",
        title: "Undoing a multiplication",
        forbid: ["group_simp", "simp"],
        text: `<p>Multiplying by <code>a</code> and then by <code>a⁻¹</code> gets you back where you started. The proof reassociates, cancels, and drops the unit: <code>rw ← mul_assoc</code> regroups the product, <code>Group.inv_mul</code> turns <code>a⁻¹ * a</code> into the unit, and <code>one_mul</code> removes it. The memberships of <code>a</code> and <code>b</code> are the side conditions of each rewrite and are found automatically.</p>`,
        statement: `theorem left_cancel (G a b : Set)
  requires group : Group(G)
  requires ha : a ∈ G.carrier
  requires hb : b ∈ G.carrier
  shows a⁻¹ * (a * b) = b`,
        starter: `sorry`,
        solution: `rw [← mul_assoc, Group.inv_mul, one_mul]
rfl`,
        hints: ["<code>rw ← mul_assoc</code> turns the goal into <code>a⁻¹ * a * b = b</code>.", "<code>rw Group.inv_mul</code> leaves <code>G.one * b = b</code>, and <code>rw one_mul</code> leaves <code>b = b</code>.", "A rewrite never closes a goal by itself; finish with <code>rfl</code>. The three rewrites fit on one line: <code>rw [← mul_assoc, Group.inv_mul, one_mul]</code>."],
      },
      {
        id: "InverseTwice",
        title: "The inverse of the inverse",
        text: `<p><code>(a⁻¹)⁻¹ = a</code> follows from the uniqueness of inverses: both <code>a</code> and <code>(a⁻¹)⁻¹</code> are inverses of <code>a⁻¹</code>. The library states it as <code>inv_inv</code>; open it in the Workbench to see the two-line argument through <code>inv_eq_of_mul_eq_one_right</code>.</p>`,
        statement: `theorem inverse_twice (G a : Set)
  requires group : Group(G)
  requires ha : a ∈ G.carrier
  shows (a⁻¹)⁻¹ = a`,
        starter: `sorry`,
        solution: `exact inv_inv with *`,
        hints: ["<code>exact inv_inv with *</code>; the <code>*</code> supplies the group and the membership of <code>a</code>."],
      },
      {
        id: "GroupSimp",
        title: "The rewrite set",
        text: `<p>A product that collapses to the unit after several cancellations is one call to <code>group_simp</code>: it applies associativity to the right and every unit and inverse cancellation until nothing changes, discharging each membership side condition from the hypotheses.</p>`,
        statement: `theorem conjugates_cancel (G a b : Set)
  requires group : Group(G)
  requires ha : a ∈ G.carrier
  requires hb : b ∈ G.carrier
  shows a * b * a⁻¹ * (a * b⁻¹ * a⁻¹) = G.one`,
        starter: `sorry`,
        solution: `group_simp`,
        hints: ["<code>group_simp</code>."],
      },
      {
        id: "UnitUnique",
        title: "The unit is unique",
        forbid: ["Identity.unique"],
        text: `<p>Underneath the bundled group lies the interface <code>Identity(A, op, e)</code>, which unfolds to <code>e ∈ A ∧ ∀ x ∈ A, op(e, x) = x ∧ op(x, e) = x</code>. Two two-sided identities for the same operation are equal: <code>e = op(e, f) = f</code>. Take both hypotheses apart with <code>obtain</code>, instantiate each law at the other unit, and one rewrite finishes.</p>`,
        statement: `theorem unit_unique (A op e f : Set)
  requires he : Identity(A, op, e)
  requires hf : Identity(A, op, f)
  shows e = f`,
        starter: `obtain ⟨eInA, eLaws⟩ := he
obtain ⟨fInA, fLaws⟩ := hf
sorry`,
        solution: `obtain ⟨eInA, eLaws⟩ := he
obtain ⟨fInA, fLaws⟩ := hf
obtain ⟨ef, fe⟩ := eLaws with f, fInA
obtain ⟨fe2, ef2⟩ := fLaws with e, eInA
rwa ← ef2`,
        hints: ["<code>obtain ⟨ef, fe⟩ := eLaws with f, fInA</code> gives <code>op(e, f) = f</code> and <code>op(f, e) = f</code>.", "<code>obtain ⟨fe2, ef2⟩ := fLaws with e, eInA</code> gives <code>op(f, e) = e</code> and <code>op(e, f) = e</code>.", "<code>rwa ← ef2</code>: rewriting <code>e</code> as <code>op(e, f)</code> leaves <code>op(e, f) = f</code>, which is <code>ef</code>."],
      },
      {
        id: "OrbitSelf",
        title: "A point lies in its orbit",
        forbid: ["orbit.self", "simp"],
        text: `<p>A group acts on a set through a hypothesis <code>act : G ↷ X</code>: the element <code>g</code> moves the point <code>x</code> to <code>g ·ₐ x</code>, and the orbit <code>orbit(x)</code> collects everything <code>x</code> is moved to. The unit moves nothing, <code>one_act</code>, and <code>orbit.act_mem</code> puts every <code>g ·ₐ x</code> into the orbit, so <code>x</code> itself lies there. The starter records that <code>G.one ·ₐ x</code> is in the orbit; state the law of the unit and rewrite with it.</p>`,
        statement: `theorem point_in_orbit (act G X x : Set)
  requires action : act : G ↷ X
  requires hx : x ∈ X
  shows x ∈ orbit(x)`,
        starter: `have group := Action.group with action
have member : G.one ·ₐ x ∈ orbit(x) := orbit.act_mem with *
sorry`,
        solution: `have group := Action.group with action
have member : G.one ·ₐ x ∈ orbit(x) := orbit.act_mem with *
have fixed : G.one ·ₐ x = x := one_act with *
rwa fixed at member`,
        hints: ["<code>have fixed : G.one ·ₐ x = x := one_act with *</code> states that the unit acts trivially.", "<code>rwa fixed at member</code> turns <code>G.one ·ₐ x ∈ orbit(x)</code> into the goal and closes it."],
      },
      {
        id: "OrbitStabilizer",
        title: "The orbit–stabilizer theorem",
        forbid: ["orbit.cardinality_dvd", "simp"],
        text: `<p>The stabilizer <code>stabilizer(x)</code> of a point is the subgroup of elements fixing it, and the orbit–stabilizer theorem says that the size of the orbit times the order of the stabilizer is the order of the group: <code>orbit_stabilizer</code>. So the size of an orbit divides the order of a finite group. The starter collects the facts that make the two sizes natural numbers and names the quotient; one application of the theorem finishes.</p>`,
        statement: `theorem orbit_size_divides (act G X x : Set)
  requires action : act : G ↷ X
  requires hx : x ∈ X
  requires finite : Finite(G)
  shows cardinality(orbit(x)) ∣ order(G)`,
        starter: `have group := Action.group with action
have subgroup := stabilizer.subgroup with *
have finiteStabilizer := Subgroup.finite with *
have stabilizerNat := cardinality.nat with finiteStabilizer
have orbitNat := cardinality.nat with (orbit.finite_of_group with *)
witness cardinality(stabilizer(x))
sorry`,
        solution: `have group := Action.group with action
have subgroup := stabilizer.subgroup with *
have finiteStabilizer := Subgroup.finite with *
have stabilizerNat := cardinality.nat with finiteStabilizer
have orbitNat := cardinality.nat with (orbit.finite_of_group with *)
witness cardinality(stabilizer(x))
exact orbit_stabilizer with *`,
        hints: ["After <code>witness</code> the goal is <code>cardinality(orbit(x)) * cardinality(stabilizer(x)) = order(G)</code>.", "<code>exact orbit_stabilizer with *</code>."],
      },
      {
        id: "Sylow",
        title: "Sylow's theorem",
        text: `<p>Sylow's first theorem: a finite group of order <code>p ^ k * m</code>, with <code>p</code> prime not dividing <code>m</code>, has a subgroup of order <code>p ^ k</code>. The library proves it by letting the group act by translation on its subsets of size <code>p ^ k</code>, of which there are <code>(p ^ k * m) choose (p ^ k)</code>, a number prime to <code>p</code>; the stabilizer of a subset in an orbit of size prime to <code>p</code> is the subgroup. Here the theorem is <code>sylow.exists_subgroup</code>, and <code>with *</code> gathers its hypotheses.</p>`,
        statement: `theorem sylow_subgroup (G : Set) (p k m : Nat)
  requires group : Group(G)
  requires finite : Finite(G)
  requires prime : Prime(p)
  requires notDivides : ¬(p ∣ m)
  requires count : order(G) = p ^ k * m
  shows ∃ P, Subgroup(P, G) ∧ cardinality(P) = p ^ k`,
        starter: `sorry`,
        solution: `exact sylow.exists_subgroup with *`,
        hints: ["<code>exact sylow.exists_subgroup with *</code>."],
      },
    ],
  },
  {
    id: "Finite",
    title: "Finite world",
    subtitle: "Counting with numerals as yardsticks.",
    imports: ["Grace.Cumulus.Cardinal"],
    intro: `<p><code>HasCardinality(A, n)</code> says <code>A</code> is in bijection with the numeral <code>n</code>, so the von Neumann numerals double as the standard finite sets. Counting theorems in Cumulus are theorems about bijections, and computation steps in whenever a numeral has to be evaluated.</p>`,
    levels: [
      {
        id: "EmptyCount",
        title: "Zero elements means empty",
        text: `<p>A set in bijection with <code>0 = ∅</code> has no members, so it is <code>∅</code>.</p>`,
        statement: `theorem empty_of_count_zero (A : Set)
  requires h : HasCardinality(A, 0)
  shows A = ∅`,
        starter: `sorry`,
        solution: `exact HasCardinality.empty_of_zero at A with h`,
        hints: ["<code>HasCardinality.empty_of_zero at A with h</code>."],
      },
      {
        id: "PowersetCount",
        title: "Eight subsets",
        text: `<p><code>powerset.cardinality</code> proves that a set with <code>n</code> elements has <code>2 ^ n</code> subsets. Its conclusion mentions <code>2 ^ 3</code>, not <code>8</code>; one <code>compute</code> bridges the gap, and <code>rw ←</code> rewrites the goal from right to left with that equation.</p>`,
        statement: `theorem eight_subsets (A : Set)
  requires h : HasCardinality(A, 3)
  shows HasCardinality(𝒫(A), 8)`,
        starter: `have eight : 2 ^ 3 = 8
  compute
sorry`,
        solution: `have eight : 2 ^ 3 = 8
  compute
rw ← eight
exact powerset.cardinality at A, 3 with h`,
        hints: ["After <code>rw ← eight</code> the goal mentions <code>2 ^ 3</code>.", "<code>exact powerset.cardinality at A, 3 with h</code>."],
      },
      {
        id: "SingletonCount",
        title: "One element",
        forbid: ["cardinality.singleton"],
        text: `<p><code>HasCardinality(A, n)</code> is <code>Nat(n) ∧ A ≃ n</code>, and <code>cardinality(A)</code> is the unique such <code>n</code>; <code>cardinality.eq_of_has</code> turns a <code>HasCardinality</code> fact into the equation. For a singleton, <code>Equipotent.singleton_one</code> gives the bijection with <code>1 = {0}</code>, and <code>typecheck</code> proves that <code>1</code> is a natural.</p>`,
        statement: `theorem one_element (x : Set)
  shows cardinality({x}) = 1`,
        starter: `have one : HasCardinality({x}, 1)
  constructor
  . sorry
  . sorry
sorry`,
        solution: `have one : HasCardinality({x}, 1)
  constructor
  . typecheck
  . exact Equipotent.singleton_one at x
exact cardinality.eq_of_has with one`,
        hints: ["The two halves are <code>typecheck</code> and <code>exact Equipotent.singleton_one at x</code>.", "Then <code>exact cardinality.eq_of_has with one</code>."],
      },
      {
        id: "AddCounts",
        title: "Counting a disjoint union",
        text: `<p>The sizes of disjoint finite sets add. <code>cardinality.union_disjoint</code> takes the two finiteness premises and <code>Disjoint(A, B)</code>, in that order. Its <code>+</code> is the addition of Computation world, so the theorem connects counting to arithmetic.</p>`,
        statement: `theorem add_counts (A B : Set)
  requires hA : Finite(A)
  requires hB : Finite(B)
  requires disjoint : Disjoint(A, B)
  shows cardinality(A ∪ B) = cardinality(A) + cardinality(B)`,
        starter: `sorry`,
        solution: `exact cardinality.union_disjoint with hA, hB, disjoint`,
        hints: ["<code>exact cardinality.union_disjoint with hA, hB, disjoint</code>."],
      },
      {
        id: "OmegaInfinite",
        title: "ω is not finite",
        text: `<p>No numeral is in bijection with the set of all numerals: every finite subset of <code>ℕ</code> is bounded, and <code>ω</code> is not. <code>omega.infinite</code> is the door to the last two worlds.</p>`,
        statement: `theorem omega_infinite
  shows ¬Finite(ω)`,
        starter: `sorry`,
        solution: `exact omega.infinite`,
        hints: ["<code>exact omega.infinite</code>."],
      },
    ],
  },
  {
    id: "Ordinals",
    title: "Ordinal world",
    subtitle: "The numerals keep going.",
    imports: ["Grace.Cumulus.Set.Hierarchy"],
    intro: `<p>An ordinal is a transitive set of transitive sets: <code>Ordinal</code> is a class, not a primitive. The numerals are ordinals, and so is <code>ω</code>, the set of all numerals. Every ordinal <code>α</code> has a successor <code>next(α) = α ∪ {α}</code>, and the whole class is well-ordered by membership. Ordinals index the cumulative hierarchy <code>V(α)</code>, defined by transfinite recursion, in which every set has a rank.</p>`,
    levels: [
      {
        id: "ZeroOrdinal",
        title: "Zero is an ordinal",
        forbid: ["Ordinal.empty"],
        text: `<p>Membership in a class is written like membership in a set, and <code>Ordinal</code> unfolds to "transitive, and every member transitive". For <code>∅</code> both halves are vacuous, and <code>simp</code> sees that once it is given the definitions and the axiom that <code>∅</code> has no members.</p>`,
        statement: `theorem zero_ordinal
  shows ∅ ∈ Ordinal`,
        starter: `sorry`,
        solution: `simp [Ordinal, Transitive, set.empty]`,
        hints: ["<code>simp [Ordinal, Transitive, set.empty]</code>."],
      },
      {
        id: "Successor",
        title: "Successors of ordinals",
        forbid: ["Ordinal.next"],
        text: `<p><code>next(α) = α ∪ {α}</code>, and <code>next.membership</code> says <code>x ∈ next(α) ↔ x ∈ α ∨ x = α</code>. With the definitions of <code>Ordinal</code>, <code>Transitive</code>, and <code>Subset</code> unfolded, the successor of an ordinal is an ordinal by pure membership logic, and <code>simp</code> finishes from the hypothesis <code>h</code>.</p>`,
        statement: `theorem successor_ordinal (α : Set)
  requires h : α ∈ Ordinal
  shows next(α) ∈ Ordinal`,
        starter: `sorry`,
        solution: `simp [Ordinal, Transitive, Subset, next.membership]`,
        hints: ["<code>simp [Ordinal, Transitive, Subset, next.membership]</code>."],
      },
      {
        id: "Numeral",
        title: "Numerals are ordinals",
        text: `<p><code>Ordinal.natural</code> covers every numeral at once. Its parameter is typed <code>Nat</code>, so the checker needs evidence that <code>3</code> is a natural; <code>with *</code> asks the elaborator to supply it.</p>`,
        statement: `theorem three_ordinal
  shows 3 ∈ Ordinal`,
        starter: `sorry`,
        solution: `exact Ordinal.natural at 3 with *`,
        hints: ["<code>exact Ordinal.natural at 3 with *</code>."],
      },
      {
        id: "Transitive",
        title: "Ordinals are transitive",
        text: `<p>A transitive set contains the members of its members. For <code>5 = {0, 1, 2, 3, 4}</code> this says each numeral below five is a subset of five. Chain two library facts: numerals are ordinals, ordinals are transitive.</p>`,
        statement: `theorem five_transitive
  shows Transitive(5)`,
        starter: `sorry`,
        solution: `have five := Ordinal.natural at 5 with *
exact Ordinal.transitive at 5 with five`,
        hints: ["First record <code>have five := Ordinal.natural at 5 with *</code>.", "Then <code>exact Ordinal.transitive at 5 with five</code>."],
      },
      {
        id: "FirstStage",
        title: "The first stage of the hierarchy",
        text: `<p><code>V</code> is defined by transfinite recursion: <code>V(0) = ∅</code>, <code>V(next(β)) = 𝒫(V(β))</code>, and a union at limits. The equations are theorems <code>V.zero</code> and <code>V.next</code>. The numeral <code>1</code> is <code>succ(0)</code>, and <code>next.natural</code> identifies <code>succ</code> with <code>next</code> on numerals.</p>`,
        statement: `theorem first_stage
  shows V(1) = 𝒫(∅)`,
        starter: `have one := next.natural at 0 with *
sorry`,
        solution: `have one := next.natural at 0 with *
rw one
have step := V.next at 0 with *
rw step
rw V.zero
rfl`,
        hints: ["<code>rw one</code> rewrites <code>1</code> as <code>next(0)</code>.", "<code>V.next at 0 with *</code> gives <code>V(next(0)) = 𝒫(V(0))</code>; rewrite with it, then with <code>V.zero</code>.", "<code>rw</code> leaves <code>𝒫(∅) = 𝒫(∅)</code>; close it with <code>rfl</code>."],
      },
      {
        id: "Omega",
        title: "ω is an ordinal",
        imports: ["Grace.Cumulus.Set.Hierarchy", "Grace.Cumulus.Nat.Foundation"],
        text: `<p><code>ω</code> is the set of all natural numbers: <code>{0, 1, 2, …}</code>, the first infinite set. It is transitive, because every member of a natural number is a natural number, and its members are transitive, because they are ordinals. Cumulus proves this as <code>Ordinal.omega</code>. Type the symbol as <code>\\omega</code>.</p>`,
        statement: `theorem omega_ordinal
  shows ω ∈ Ordinal`,
        starter: `sorry`,
        solution: `exact Ordinal.omega`,
        hints: ["<code>exact Ordinal.omega</code>."],
      },
      {
        id: "Limit",
        title: "ω is a limit",
        imports: ["Grace.Cumulus.Set.Hierarchy", "Grace.Cumulus.Nat.Foundation"],
        text: `<p>A limit ordinal is a nonempty ordinal closed under successor: no largest member, no predecessor of its own. <code>ω</code> is the first one, and the hierarchy's definition of <code>V</code> takes a union there instead of a powerset. Open <code>Limit.omega</code> in the Workbench to see both halves proved from <code>nat.omega</code> and <code>next.natural</code>.</p>`,
        statement: `theorem omega_limit
  shows Limit(ω)`,
        starter: `sorry`,
        solution: `exact Limit.omega`,
        hints: ["<code>exact Limit.omega</code>."],
      },
      {
        id: "Trichotomy",
        title: "Any two ordinals compare",
        text: `<p>Ordinals are totally ordered by membership: for ordinals <code>α</code> and <code>β</code>, one of <code>α ∈ β</code>, <code>α = β</code>, <code>β ∈ α</code> holds. The library states this with the premises inside the conclusion, so feed them with <code>with</code>.</p>`,
        statement: `theorem compare (α β : Set)
  requires ha : α ∈ Ordinal
  requires hb : β ∈ Ordinal
  shows α ∈ β ∨ α = β ∨ β ∈ α`,
        starter: `sorry`,
        solution: `exact Ordinal.trichotomy at α with ha, β, hb`,
        hints: ["<code>Ordinal.trichotomy at α</code> then supply <code>ha</code>, the term <code>β</code>, and <code>hb</code> in that order."],
      },
      {
        id: "BuraliForti",
        title: "There is no set of all ordinals",
        imports: ["Grace.Cumulus.Set"],
        forbid: ["Ordinal.no_set_of_all"],
        text: `<p>The Burali-Forti paradox, made a theorem. If a set <code>X</code> contained every ordinal, then <code>ordinalsWithin(X)</code>, the ordinals among its members, would itself be an ordinal (<code>ordinalsWithin.ordinal</code>), hence a member of <code>X</code>, hence a member of itself, against Paradox world. The class <code>Ordinal</code>, like <code>Universe</code>, is proper.</p>`,
        statement: `theorem no_set_of_all_ordinals
  shows ¬(∃ X, ∀ α, α ∈ Ordinal → α ∈ X)`,
        starter: `intro h
obtain ⟨X, hX⟩ := h
have ordinal := ordinalsWithin.ordinal with hX
sorry`,
        solution: `intro h
obtain ⟨X, hX⟩ := h
have ordinal := ordinalsWithin.ordinal with hX
have inX := hX with ordinalsWithin(X), ordinal
have self : ordinalsWithin(X) ∈ ordinalsWithin(X)
  apply ordinalsWithin.membership.backward
  exact ⟨inX, ordinal⟩
exact membership.irreflexive with self`,
        hints: ["<code>have inX := hX with ordinalsWithin(X), ordinal</code> puts the set inside <code>X</code>.", "<code>ordinalsWithin.membership.backward</code> needs <code>⟨inX, ordinal⟩</code> and gives self-membership.", "Finish with <code>membership.irreflexive with self</code>."],
      },
    ],
  },
  {
    id: "Infinite",
    title: "Infinite world",
    subtitle: "Some infinities are larger than others.",
    imports: ["Grace.Cumulus.Cardinal", "Grace.Cumulus.Rat", "Grace.Cumulus.Real"],
    intro: `<p>Sizes of infinite sets are compared by injections: <code>A ≼ B</code> when <code>A</code> injects into <code>B</code>, and <code>A ≃ B</code> when there is a bijection. <code>Countable(A)</code> means <code>A ≼ ℕ</code>. Cantor's theorem shows no set is as large as its own powerset, so <code>𝒫(ℕ)</code> is uncountable, and from there the reals. These levels apply the Cumulus theorems that make up the whole argument; open any of them in the Workbench to read the proof.</p>`,
    levels: [
      {
        id: "EquipotentReflexive",
        title: "A set is as large as itself",
        forbid: ["Equipotent.reflexive"],
        text: `<p><code>A ≃ B</code>, typed <code>\\simeq</code>, means there is a bijection from <code>A</code> to <code>B</code>: it unfolds to <code>∃ f, BijectiveBetween(f, A, B)</code>. An existential goal is proved by naming a witness with <code>witness</code> and proving the property of it. The identity function is the witness here, and Function world already proved that it is a bijection.</p>`,
        statement: `theorem equipotent_reflexive (A : Set)
  shows A ≃ A`,
        starter: `witness identity(A)
sorry`,
        solution: `witness identity(A)
exact identity.bijective at A`,
        hints: ["After <code>witness identity(A)</code> the goal is <code>BijectiveBetween(identity(A), A, A)</code>.", "<code>exact identity.bijective at A</code>."],
      },
      {
        id: "EquipotentSymmetric",
        title: "Bijections run both ways",
        forbid: ["Equipotent.symmetric"],
        text: `<p>An existential hypothesis is taken apart with <code>obtain ⟨f, hf⟩</code>, which names the bijection. The bijection back is its converse relation, <code>converse(f, A, B)</code>, and <code>converse.bijective</code> says it is again a bijection.</p>`,
        statement: `theorem equipotent_symmetric (A B : Set)
  requires h : A ≃ B
  shows B ≃ A`,
        starter: `obtain ⟨f, hf⟩ := h
sorry`,
        solution: `obtain ⟨f, hf⟩ := h
witness converse(f, A, B)
exact converse.bijective with hf`,
        hints: ["<code>witness converse(f, A, B)</code>.", "<code>exact converse.bijective with hf</code>."],
      },
      {
        id: "DominatedTransitive",
        title: "Injections compose",
        forbid: ["Dominated.transitive"],
        text: `<p><code>A ≼ B</code>, typed <code>\\preceq</code>, means there is an injection from <code>A</code> into <code>B</code>: <code>A</code> is no larger than <code>B</code>. Two injections compose to an injection, so the relation is transitive. Take both hypotheses apart, offer the composite as the witness, and apply <code>compose.injective</code>.</p>`,
        statement: `theorem dominated_transitive (A B C : Set)
  requires hAB : A ≼ B
  requires hBC : B ≼ C
  shows A ≼ C`,
        starter: `obtain ⟨f, hf⟩ := hAB
obtain ⟨g, hg⟩ := hBC
sorry`,
        solution: `obtain ⟨f, hf⟩ := hAB
obtain ⟨g, hg⟩ := hBC
witness compose(g, f, A, B, C)
exact compose.injective with hf, hg`,
        hints: ["<code>witness compose(g, f, A, B, C)</code>.", "<code>exact compose.injective with hf, hg</code>."],
      },
      {
        id: "PowersetAbove",
        title: "The powerset is at least as large",
        forbid: ["Dominated.powerset"],
        text: `<p><code>x ↦ {x}</code> injects any set into its powerset. Cumulus defines that map as the function graph <code>singletonMap(A)</code> and proves it injective. This is the easy half of Cantor's theorem; the next level is the hard half.</p>`,
        statement: `theorem powerset_above (A : Set)
  shows A ≼ 𝒫(A)`,
        starter: `sorry`,
        solution: `witness singletonMap(A)
exact singletonMap.injective at A`,
        hints: ["<code>witness singletonMap(A)</code>.", "<code>exact singletonMap.injective at A</code>."],
      },
      {
        id: "Cantor",
        title: "Cantor's diagonal argument",
        forbid: ["Cantor.no_surjection_onto_powerset", "Cantor.powerset_not_dominated"],
        text: `<p>No function <code>f</code> from <code>A</code> to <code>𝒫(A)</code> is onto. The diagonal set <code>cantorDiagonal(f, A) = { x ∈ A | x ∉ f(x) }</code> is a subset of <code>A</code>, so if <code>f</code> were onto some <code>d</code> would be sent to it, and then <code>d</code> belongs to the diagonal set exactly when it does not. The starter sets up <code>d</code>, the equation <code>value : f(d) = cantorDiagonal(f, A)</code>, the membership law <code>shape</code>, and the case split; each case is a two- or three-line contradiction.</p>`,
        statement: `theorem no_surjection_onto_powerset (f A : Set)
  shows ¬SurjectiveBetween(f, A, 𝒫(A))`,
        starter: `intro surjective
obtain ⟨function, onto⟩ := surjective
have diagonalIn := cantorDiagonal.in_powerset at f, A
obtain ⟨d, dInA, hits⟩ := onto with cantorDiagonal(f, A), diagonalIn
have value := FunctionBetween.apply_value with function, dInA, hits
have shape := cantorDiagonal.membership at d, f, A
have split : d ∈ cantorDiagonal(f, A) ∨ d ∉ cantorDiagonal(f, A) by tauto
cases split with inside | outside
. sorry
. sorry`,
        solution: `intro surjective
obtain ⟨function, onto⟩ := surjective
have diagonalIn := cantorDiagonal.in_powerset at f, A
obtain ⟨d, dInA, hits⟩ := onto with cantorDiagonal(f, A), diagonalIn
have value := FunctionBetween.apply_value with function, dInA, hits
have shape := cantorDiagonal.membership at d, f, A
have split : d ∈ cantorDiagonal(f, A) ∨ d ∉ cantorDiagonal(f, A) by tauto
cases split with inside | outside
. have facts := shape.forward with inside
  rw value at facts
  exact facts.right with inside
. apply outside
  apply shape.backward
  constructor
  . exact dInA
  . rw value
    exact outside`,
        hints: ["Inside: <code>have facts := shape.forward with inside</code> says <code>d ∈ A ∧ d ∉ f(d)</code>; <code>rw value at facts</code> turns <code>f(d)</code> into the diagonal set, and <code>facts.right</code> contradicts <code>inside</code>.", "Outside: <code>apply outside</code>, then <code>apply shape.backward</code> and <code>constructor</code>; the first goal is <code>dInA</code>, and the second becomes <code>outside</code> after <code>rw value</code>."],
      },
      {
        id: "SchroederBernstein",
        title: "Schröder–Bernstein",
        text: `<p>If each of two sets injects into the other, they are in bijection. This is one of the Top 100 theorems and the hard theorem of this world: Cumulus proves it by the chain construction, in several hundred lines. Apply it here, and open <code>Dominated.antisymmetric</code> in the Workbench to follow <code>bernsteinMap</code> back to the construction.</p>`,
        statement: `theorem schroeder_bernstein (A B : Set)
  requires hAB : A ≼ B
  requires hBA : B ≼ A
  shows A ≃ B`,
        starter: `sorry`,
        solution: `exact Dominated.antisymmetric with hAB, hBA`,
        hints: ["<code>exact Dominated.antisymmetric with hAB, hBA</code>."],
      },
      {
        id: "NaturalsCountable",
        title: "ℕ is countable",
        forbid: ["naturals.countable"],
        text: `<p><code>Countable(A)</code> unfolds to <code>∃ f, InjectiveBetween(f, A, ℕ)</code>. For <code>ℕ</code> itself the identity is the injection.</p>`,
        statement: `theorem naturals_countable
  shows Countable(ℕ)`,
        starter: `sorry`,
        solution: `witness identity(ℕ)
exact identity.injective at ℕ`,
        hints: ["<code>witness identity(ℕ)</code>.", "<code>exact identity.injective at ℕ</code>."],
      },
      {
        id: "RationalsCountable",
        title: "ℚ is countable",
        text: `<p>Rationals are equivalence classes of fraction representatives, pairs of naturals with a sign; pairs of naturals are countable by the pairing function, and quotients of countable sets are countable. The library theorem assembles those three facts.</p>`,
        statement: `theorem rationals_countable
  shows Countable(ℚ)`,
        starter: `sorry`,
        solution: `exact rationals.countable`,
        hints: ["<code>exact rationals.countable</code>."],
      },
      {
        id: "PowersetUncountable",
        title: "𝒫(ℕ) is uncountable",
        text: `<p>An injection of <code>𝒫(ℕ)</code> into <code>ℕ</code> would turn around into a surjection of <code>ℕ</code> onto <code>𝒫(ℕ)</code>, against the diagonal argument you proved four levels ago. <code>Uncountable</code> is <code>¬Countable</code>.</p>`,
        statement: `theorem powerset_uncountable
  shows Uncountable(𝒫(ℕ))`,
        starter: `sorry`,
        solution: `exact powerset.naturals_uncountable`,
        hints: ["<code>exact powerset.naturals_uncountable</code>."],
      },
      {
        id: "RealsUncountable",
        title: "ℝ is uncountable",
        text: `<p>The reals are Dedekind cuts of rationals, and Cantor's diagonal argument runs over their binary expansions. This is the last theorem of the game and one of the Top 100; open <code>reals.uncountable</code> in the Workbench to read the construction, and then the rest of Cumulus is yours.</p>`,
        statement: `theorem reals_uncountable
  shows Uncountable(ℝ)`,
        starter: `sorry`,
        solution: `exact reals.uncountable`,
        hints: ["<code>exact reals.uncountable</code>."],
      },
    ],
  },
];
