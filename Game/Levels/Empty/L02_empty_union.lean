import Game.Levels.Empty.L01_empty_set

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter mem_setOf)
open TopologicalSpace
open STG4

World "Empty"
Level 2
Title "The empty union"

Introduction "
We show that the union over the empty family of sets is the empty set.

Now that you have completed the Family Union world, you know have to deal with unions of families of sets.
"

/-- The union over the empty family of sets is the empty set. I.e., $⋃ ∅ = ∅$. -/
TheoremDoc sUnionEmpty as "sUnionEmpty" in "∅"

/-- The union over the empty family of sets is the empty set. -/
Statement sUnionEmpty {X : Type} : ⋃₀ (∅ : Set (Set X)) = (∅ : Set X)  := by
  Hint "To begin with, you can either use `ext x` or `Subset.antisymm`. If you use `Subset.antisymm`, you can use the theorem `EmptySubset` from the previous subset to prove one of the inclusions."
  apply Subset.antisymm
  intro U h
  Hint (hidden := true ) "Recall that the theorem `mem_sUnion` unfolds the definition of membership in a union over a family of sets."
  rw [mem_sUnion] at h
  obtain ⟨t, h1, _⟩ := h
  by_contra
  exact Set.not_mem_empty t h1

  apply EmptySubset
