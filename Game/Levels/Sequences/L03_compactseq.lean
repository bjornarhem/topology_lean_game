import Game.Levels.Sequences.L02_finitenotin

open Set
namespace TTG

World "Sequences"
Level 3
Title "Compactness of a Sequence"

Introduction
"
This level links the definition of convergence with that of compactness.
We strongly encourage you to first attempt to handwrite the proof.
Pressing \"Show more help!\" afterwards will allow you to check your proof.

At some point in your proof, you will need to use the theorem `Set.finite_singleton`.
"

/--Any singleton is finite.-/
TheoremDoc Set.finite_singleton as "Set.finite_singleton" in "Finite"
NewTheorem Set.finite_singleton

/--
If $s_n$ is a sequence that converges to $t$, then the set ${t} ∪ \{s_n | n} is compact.$
-/
Statement {X : Type} [TopologicalSpace X] (s : ℕ → X) (t : X) (hst : ConvergesTo s t) : IsCompact ({t} ∪ {s n | n}) := by
  Hint (hidden := true) "Consider $F$ an arbitrary open cover of $\{t} ∪ \{s_n | n}$.
  In particular, there must exist an open $U ∈ F$ such that $t$ in $U$.
  Since $s_n ⟶ t$, by the previous exercise, $s_n ∈ U$ for all but finitely many $n$."
  Hint (hidden := true) "Construct a finite subcover as follows:
  For each element $s_n$ such that $s_n ∉ U$, add an open $V_x ∈ F$ for which $x ∈ V x$.
  Then add $U$. Why is this a finite subcover of $F$?
  "
  intro F Fopen Fcover
  Hint "Start by proving `∃ U ∈ {F}, {t} ∈ U` before extracting `U` with `obtain`."
  have : ∃ U ∈ F, t ∈ U := by
    have : t ∈ ⋃₀ F := by
      apply Fcover; left; rw [mem_singleton_iff]
    rw [mem_sUnion] at this
    exact this
  obtain ⟨U, UinF, tinU⟩ := this
  Hint "Now prove `\{x | ∃ n, s n ∉ U ∧ s n = x} ⊆ ⋃₀ F`, i.e.
  that $F$ covers all the elements $s_n$ for which $s_n ∉ U.
  Look back on the proof - why do we care about these elements specifically?"
  have Fcover' : {x | ∃ n, s n ∉ U ∧ s n = x} ⊆ ⋃₀ F := by
    Hint "Keep in mind that
    `\{x | ∃ n, {s} n ∉ {U} ∧ {s} n = x} ⊆ \{x | ∃ n, {s} n = x}`,
    `\{x | ∃ n, {s} n = x} ⊆ \{{t}} ∪ \{x | ∃ n, {s} n = x}` and
    `\{{t}} ∪ \{x | ∃ n, {s} n = x} ⊆ ⋃₀ {F}`.
    "
    Hint (hidden := true) "Write `apply Subset.trans (B := \{x | ∃ n, s n = x})`.
    Look up the definition of `Subset.trans` in the \"Theorems\" tab to understand why we used `B`."
    apply Subset.trans (B := {x | ∃ n, s n = x})
    · intro x hx
      rw [mem_setOf] at *
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, hn.right⟩
    · apply Subset.trans (B := {t} ∪ {x | ∃ n, s n = x})
      · intro x hx; right; exact hx
      · exact Fcover
  Hint "We suggest adding a hypothesis that is fundamentally spelling out {Fcover'} more concretely:
  `∀ x ∈ \{x | ∃ n, {s} n ∉ {U} ∧ {s} n = x}, ∃ V ∈ {F}, x ∈ V`.
  Having the hypothesis under this form makes it easier to use with `choose!`"
  have : ∀ x ∈ {x | ∃ n, s n ∉ U ∧ s n = x}, ∃ V ∈ F, x ∈ V := by
    intro x hx
    have := Fcover' hx
    rw [mem_sUnion] at this
    exact this
  Hint "Now you can use `choose!` with {this}."
  choose! V hV using this
  Hint "At this point you have retrieved all the necessary objects
  to specify a finite open subcover of {F}."
  Hint (hidden := true) "Write `use \{{U}} ∪ ({V} '' \{x | ∃ n, {s} n ∉ {U} ∧ {s} n = x})`."
  use {U} ∪ (V '' {x | ∃ n, s n ∉ U ∧ s n = x})
  Hint "Split the goals with `constructor`."
  constructor
  · -- Prove it is included in the original cover.
    Hint "First you have to prove that it is included in the original cover {F}."
    intro W hW
    Hint (hidden := true) "Split {hW} into two cases."
    rcases hW with hW | hW
    · rw [mem_singleton_iff] at hW; rw [hW]; exact UinF
    · rw [Set.mem_image] at hW
      obtain ⟨x, hx, rfl⟩ := hW
      exact (hV x hx).left
  · constructor
    · -- Prove it is finite.
      Hint "Now you have to prove that your subcover is finite."
      apply Finite.union
      · exact Set.finite_singleton U
      · apply Finite.image
        Hint "This part is trickier. Our goal basically says that $\{{s}_n | {s}_n ∉ {U}}$ is finite,
        `ConvergesTo.finite_setOf_notMem` tells use that $\{n |{s}_n ∉ {U}} is finite. Notice the difference between the two sets.
        You can solve this by stating that $$\{n | {s}_n ∉ {U}}$ is the image of $\{{s}_n | {s}_n ∉ {U}}$ under $s$."
        Hint (hidden := true) "Prove: `\{x | ∃ n, {s} n ∉ {U} ∧ {s} n = x} = {s} '' \{n | {s} n ∉ {U}}`"
        have : {x | ∃ n, s n ∉ U ∧ s n = x} = s '' {n | s n ∉ U} := by
          rfl
        rw [this]
        apply Finite.image
        exact ConvergesTo.finite_setOf_notMem s t hst U (Fopen U UinF) tinU
    · -- Prove it remains a cover.
      Hint "Now you have to prove that the subcover indeed remains a cover."
      intro x hx
      rw [mem_sUnion]
      Hint "You must treat three cases: `{x} = {t}`, `{x} ∈ \{x | ∃ n, {s} n = x} ∧ {s} n ∈ {U}`, and `{x} ∈ \{x | ∃ n, {s} n = x} ∧ {s} n ∉ {U}`."
      Hint (hidden := true) "First split {hx} with `rcases`."
      rcases hx with hx | hx
      · -- If x = t
        Hint (hidden := true) "{x} ∈ {U}"
        use U
        constructor
        · left; rw [mem_singleton_iff]
        · rw [mem_singleton_iff] at hx; rw [hx]; exact tinU
      · -- If x ≠ t
        rw [mem_setOf] at hx
        obtain ⟨n, rfl⟩ := hx
        Hint (hidden := true) "Use `by_cases` on `{s} {n} ∈ {U}`."
        by_cases snU : s n ∈ U
        · -- If x ∈ U
          Hint (hidden := true) "{s} {n} ∈ {U}"
          use U
          constructor
          · left; rw [mem_singleton_iff]
          · exact snU
        · -- If x ∉ U
          Hint (hidden := true) "{s} {n} ∈ {V} ({s} {n})"
          use V (s n)
          constructor
          · right; rw [mem_image]; use s n; rw [mem_setOf]
            constructor
            · exact ⟨n, snU, rfl⟩
            · rfl
          · exact (hV (s n) ⟨n, snU, rfl⟩).right
