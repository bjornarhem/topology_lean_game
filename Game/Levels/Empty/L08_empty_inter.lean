import Game.Levels.Empty.L07_nonempty_image

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
namespace TTG

World "Empty"
Level 8
Title "Intersection with the empty set"

Introduction "
In this level, we show that the intersection of any set with the empty set is empty.
"

/-- For any set $U$, $∅ ∩ U = ∅$. -/
TheoremDoc TTG.empty_inter as "empty_inter" in "∅"

/-- For any set $U$, $∅ ∩ U = ∅$. -/
Statement empty_inter {X : Type} (A : Set X) : (∅ ∩ A = ∅) := by
  Hint (hidden:=true) "Remember that you can `apply Subset.antisymm` to prove that two sets are equal. This changes the goal into two subset inclusions. Do you see how one of them follows directly from something you've already proven?"
  apply Subset.antisymm
  intro x h
  rw [mem_inter_iff] at h
  exact h.left

  apply empty_subset
