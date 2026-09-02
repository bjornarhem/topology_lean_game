import Game.Levels.Empty.L04_nonempty

open Set
namespace TTG

World "Empty"
Level 5
Title "Preimage of the empty set"

Introduction "
In this level, we show that the preimage of the empty set under any function is the empty set.
"

/-- If $f : X → Y$ is any function, then $f^{-1}(∅) = ∅$. -/
TheoremDoc TTG.empty_preimage as "empty_preimage" in "∅"

/-- If $f : X → Y$ is any function, then $f^{-1}(∅) = ∅$. -/
Statement empty_preimage {X Y : Type} (f : X → Y) : f⁻¹' (∅) = ∅ := by
  Hint "At some point in this proof, you might end up with a hypothesis `h : f x ∈ ∅`. In this case, `Set.notMem_empty (f x) h` is a proof of `False`. Thus, `by_contra` followed by `exact Set.notMem_empty (f x) h` is one way to finish the proof. However, this also works if you don't write `by_contra` first. This is because `x ∈ ∅` is definitionally equal to `False`."
  apply Subset.antisymm
  intro x h
  rw [Set.mem_preimage] at h
  by_contra
  exact Set.notMem_empty (f x) h

  apply empty_subset
