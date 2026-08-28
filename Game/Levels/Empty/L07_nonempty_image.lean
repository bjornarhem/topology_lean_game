import Game.Levels.Empty.L06_empty_image

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
namespace TTG

World "Empty"
Level 7
Title "Image of a nonempty empty set"

Introduction "
In this level, we show that the image of a nonempty set under any function is nonempty.
"

/-- If $f : X → Y$ is any function, and $U ⊆ X$ is nonempty, then $f(U)$ is nonempty. -/
TheoremDoc TTG.nonempty_image as "nonempty_image" in "∅"

/-- If $f : X → Y$ is any function, and $U ⊆ X$ is nonempty, then $f(U)$ is nonempty. -/
Statement nonempty_image {X Y : Type} (f : X → Y) (A : Set X) : A.Nonempty → (f '' (A)).Nonempty := by
  intro h
  obtain ⟨x, h1⟩ := h
  rw [Set.nonempty_def]
  use f x
  exact ⟨x, h1, rfl⟩
