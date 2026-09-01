import Game.Levels.Empty.L01_empty_set

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
namespace TTG

World "Empty"
Level 2
Title "The empty union"

Introduction "
We show that the union over the empty family of sets is the empty set.

Now that you have completed the Family Union world, you know have to deal with unions of families of sets.
"

/-- The union over the empty family of sets is the empty set. I.e., $⋃ ∅ = ∅$. -/
TheoremDoc TTG.sUnion_empty as "sUnion_empty" in "∅"

/-- The union over the empty family of sets is the empty set. -/
Statement sUnion_empty {X : Type} : ⋃₀ (∅ : Set (Set X)) = (∅ : Set X)  := by
  Hint "To begin with, you can either use `ext x` or `Subset.antisymm`. If you use `Subset.antisymm`, you can use the theorem `empty_subset` from the previous subset to prove one of the inclusions."
  apply Subset.antisymm
  intro U h
  Hint (hidden := true ) "Recall that the theorem `mem_sUnion` unfolds the definition of membership in a union over a family of sets."
  rw [mem_sUnion] at h
  obtain ⟨t, h1, _⟩ := h
  by_contra
  exact Set.notMem_empty t h1

  apply empty_subset
