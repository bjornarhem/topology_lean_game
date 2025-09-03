import Game.Levels.Empty.L07_nonempty_image

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Empty"
Level 8
Title "Intersection with the empty set"

Introduction "
In this level, we show that the intersection of any set with the empty set is empty.
"

/-- For any set $U$, $∅ ∩ U = ∅$. -/
TheoremDoc EmptyInter as "EmptyInter" in "∅"

/-- For any set $U$, $∅ ∩ U = ∅$. -/
Statement EmptyInter {X : Type} (A : Set X) : (∅ ∩ A = ∅) := by
  apply Subset.antisymm
  intro x h
  rw [mem_inter_iff] at h
  exact h.left

  apply EmptySubset
