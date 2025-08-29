import Game.Levels.Spaces.L01_spaces

open Set (mem_inter_iff mem_union Subset.antisymm)
open TopologicalSpace
open STG4

World "Spaces"
Level 2
Title "Closed sets"

Introduction "
In this level we introduce closed sets.
In Lean, the predicate `IsClosed` asserts that a set is closed.
If U is a set in a topological space X, then `IsClosed U` is defined as `IsOpen Uᶜ`,
where `Uᶜ` is the complement of U.

You can use the theorem `isOpen_compl_iff` to rewrite `IsClosed U` as `IsOpen Uᶜ`, and vice versa.
"

/-- Show that if $U$ and $V$ are closed sets in $X$, then $U ∪ V$ is closed. -/
Statement {X : Type} [h : TopologicalSpace X] (U V : Set X) : (IsClosed U) → (IsClosed V) → IsClosed (U ∪ V) := by
  Hint "In this level, you can use the theorem `compl_union`, that you proved in Combination World, to rewrite ` (U ∪ V)ᶜ` as `Uᶜ ∩ Vᶜ`."
  Hint "You can use `rw [← isOpen_compl_iff]` to rewrite `IsClosed U` as `IsOpen Uᶜ`."
  intro hU hV
  rw [← isOpen_compl_iff]
  Hint "Here it would be a good idea to use the theorem `compl_union`."
  rw [compl_union]
  rw [← isOpen_compl_iff] at hU hV

  apply h.isOpen_inter
  exact hU
  exact hV

/-- $U^c$ is open if and only if $U$ is closed. -/
TheoremDoc isOpen_compl_iff as "isOpen_compl_iff" in "topology"

NewTheorem isOpen_compl_iff
