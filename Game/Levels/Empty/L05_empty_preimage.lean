import Game.Levels.Empty.L04_nonempty

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter mem_setOf)
open TopologicalSpace
open STG4

World "Empty"
Level 5
Title "Preimage of the empty set"

Introduction "
In this level, we show that the preimage of the empty set under any function is the empty set.
"

/-- If $f : X → Y$ is any function, then $f^{-1}(∅) = ∅$. -/
TheoremDoc EmptyPreimage as "EmptyPreimage" in "∅"

/-- If $f : X → Y$ is any function, then $f^{-1}(∅) = ∅$. -/
Statement EmptyPreimage {X Y : Type} (f : X → Y) : f⁻¹' (∅) = ∅ := by
  Hint "At some point in this proof, you might end up with a hypothesis `h : f x ∈ ∅`. In this case, `Set.not_mem_empty (f x) h` is a proof of `false`. Thus, `by_contra` followed by `exact Set.not_mem_empty (f x) h` is one way to finish the proof. However, this also works if you don't write `by_contra` first. This is because Lean recognizes that `false` is sufficient to prove anything, so `exact false` is a proof of any statement. Do you see why `false` should imply any statement?"
  apply Subset.antisymm
  intro x h
  rw [Set.mem_preimage] at h
  by_contra
  exact Set.not_mem_empty (f x) h

  apply EmptySubset
