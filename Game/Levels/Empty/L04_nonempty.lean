import Game.Levels.Empty.L03_empty_open

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Empty"
Level 4
Title "Nonempty sets"

Introduction "
In this level, we introduce nonempty sets.

A set is nonempty if it contains at least one element.
Specifically, for a set `S`, `S.Nonempty` is defined as `∃ x, x ∈ S`.
Whenever you have a hypothesis `h : S.Nonempty` (or `h : Set.Nonempty S`),
you can use `obtain ⟨x, h1⟩ := h` to get an element `x` and a proof `h1` that `x ∈ S`.

You can also use the theorem `Set.nonempty_def` to rewrite `S.Nonempty` into `∃ x, x ∈ S` and vice versa.
"

/-- A set is nonempty if and only if it is not equal to the empty set. -/
TheoremDoc NonemptyIffNotEmpty as "NonemptyIffNotEmpty" in "∅"

/-- Show that a set is nonempty if and only if it is not equal to the empty set. -/
Statement NonemptyIffNotEmpty {X : Type} (A : Set X) : A.Nonempty ↔ ¬ (A = ∅):= by
  Hint (hidden := true) "Try using `push_neg`."
  push_neg
  rfl

/--
For a set `S`, `S.Nonempty` is defined as `∃ x, x ∈ S`.
Whenever you have a hypothesis `h : S.Nonempty` (or `h : Set.Nonempty S`),
you can use `obtain ⟨x, h1⟩ := h` to get an element `x` and a proof `h1` that `x ∈ S`.
-/
DefinitionDoc Set.Nonempty as "Set.Nonempty"
NewDefinition Set.Nonempty

/--
A set $S$ is nonempty if and only if there exists an element $x$ such that $x ∈ S$.
-/
TheoremDoc Set.nonempty_def as "Set.nonempty_def" in "∅"
NewTheorem Set.nonempty_def
