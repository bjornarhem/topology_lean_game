import Game.Levels.Spaces.L05_interclosed

open TopologicalSpace

namespace TTG

World "Spaces"
Level 6
Title "Union of Two Open Sets"

Introduction "

"

/-- If $U$ and $V$ are open sets, then $U ∪ V$ is also open. -/
TheoremDoc TTG.IsOpen.union as "IsOpen.union" in "topology"

/-- -/
Statement IsOpen.union {X : Type} [h : TopologicalSpace X] (U V : Set X) : IsOpen U → IsOpen V → IsOpen (U ∪ V) := by
  intro hU hV
  have hUV : ∀ A ∈ {U, V}, IsOpen A := by
    rintro A (rfl | rfl)
    · exact hU
    · exact hV
  have := isOpen_sUnion hUV
  rwa [←sUnion_pair] at this
