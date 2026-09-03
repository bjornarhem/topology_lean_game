import Game.Levels.Spaces.L06_pairopen

open Set

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
  Hint "Repeat the strategy from the previous exercise."
  intro hU hV
  Hint (hidden := true) "Prove `∀ A ∈ \{U, V}, IsClosed A`."
  have hUV : ∀ A ∈ {U, V}, IsClosed A := by
    intro A hA
    rcases hA with rfl | rfl
    · exact hU
    · exact hV
  have := isClosed_sInter hUV
  rw [←sInter_pair] at this
  exact this
