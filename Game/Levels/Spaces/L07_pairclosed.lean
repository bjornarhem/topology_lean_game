import Game.Levels.Spaces.L06_pairopen

open TopologicalSpace

namespace TTG

World "Spaces"
Level 7
Title "Intersection of Two Closed Sets"

Introduction "
Here we ask you to prove the symmetric result of the previous exercise.
"

/-- If $U$ and $V$ are closed sets, then $U ∩ V$ is also closed. -/
TheoremDoc TTG.IsClosed.inter as "IsClosed.inter" in "topology"

/-- If $U$ and $V$ are closed sets, then $U ∩ V$ is also closed. -/
Statement IsClosed.inter {X : Type} [h : TopologicalSpace X] (U V : Set X) : IsClosed U → IsClosed V → IsClosed (U ∩ V) := by
  intro hU hV
  have hUV : ∀ A ∈ {U, V}, IsClosed A := by
    rintro A (rfl | rfl)
    · exact hU
    · exact hV
  have := isClosed_sInter hUV
  rwa [←sInter_pair] at this
