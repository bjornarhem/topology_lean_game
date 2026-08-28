import Game.Levels.Empty.L05_empty_preimage

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
namespace TTG

World "Empty"
Level 6
Title "Image of the empty set"

Introduction "
In this level, we show that the image of the empty set under any function is the empty set.
"

/-- If $f : X → Y$ is any function, then $f(∅) = ∅$. -/
TheoremDoc TTG.empty_image as "empty_image" in "∅"

/-- If $f : X → Y$ is any function, then $f(∅) = ∅$. -/
Statement empty_image {X Y : Type} (f : X → Y) : f '' (∅) = ∅ := by
  apply Subset.antisymm
  intro y h
  obtain ⟨x, h1, rfl⟩ := h
  exact Set.not_mem_empty x h1

  apply empty_subset
