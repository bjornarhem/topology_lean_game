import Game.Levels.Empty.L05_empty_preimage

open Set
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
  Hint (hidden:=true) "Remember that you can `apply Subset.antisymm` to prove that two sets are equal. This changes the goal into two subset inclusions. Do you see how one of them follows directly from something you've already proven?"
  apply Subset.antisymm
  intro y h
  Hint (hidden:=true) "Do you remember what to do when you have a hypothesis of the form `{y} ∈ f '' A` for some set `A`? You can always look in the definition tab if you forget how to work with a definition such as `f '' A`."
  obtain ⟨x, h1, rfl⟩ := h
  exact Set.notMem_empty x h1

  apply empty_subset
