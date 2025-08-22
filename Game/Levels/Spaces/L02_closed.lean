import Game.Metadata

World "Spaces"
Level 2
Title "Closed sets"

Introduction "
TODO: explain
"

open Set TopologicalSpace
namespace topology

/-- Show that if $U$ and $V$ are closed sets in $X$, then $U ∪ V$ is closed. -/
Statement ClosedUnion {X : Type} [h : TopologicalSpace X] (U V : Set X) : (IsClosed U) → (IsClosed V) → IsClosed (U ∪ V) := by
  Hint "In this level, you can use `Set.compl_union` to rewrite ` (U ∪ V)ᶜ` as `Uᶜ ∩ Vᶜ`."
  intro hU hV
  rw [← isOpen_compl_iff]
  rw [compl_union]
  rw [← isOpen_compl_iff] at hU hV

  apply h.isOpen_inter
  exact hU
  exact hV

NewTheorem Set.compl_union isOpen_compl_iff
