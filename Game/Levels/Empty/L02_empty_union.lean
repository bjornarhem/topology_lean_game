import Game.Levels.Empty.L01_empty_set

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter mem_setOf)
open TopologicalSpace
open STG4

World "Empty"
Level 2
Title "The empty union"

Introduction "
We show that the union over the empty family of sets is the empty set.
"

/-- The union over the empty family of sets is the empty set. I.e., $⋃ ∅ = ∅$. -/
TheoremDoc sUnionEmpty as "sUnionEmpty" in "∅"

/-- The union over the empty family of sets is the empty set. -/
Statement sUnionEmpty {X : Type} : ⋃₀ (∅ : Set (Set X)) = (∅ : Set X)  := by
  -- TODO: add hints
  apply Subset.antisymm
  intro U h
  rw [mem_sUnion] at h
  obtain ⟨t, h1, _⟩ := h
  by_contra
  exact Set.not_mem_empty t h1

  apply EmptySubset
