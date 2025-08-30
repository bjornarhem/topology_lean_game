import Game.Levels.Empty.L02_empty_union

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter mem_setOf)
open TopologicalSpace
open STG4

World "Empty"
Level 3
Title "The empty set is open"

Introduction "
In this level, show that the empty set is open in any topological space.
"

/-- Let $X$ be a topological space. Then $\emptyset \subseteq X$ is open. -/
Statement {X : Type} [h : TopologicalSpace X] : IsOpen (∅ : Set X) := by
  -- TODO: add hint that you can use sUnionEmpty
  have h1 := h.isOpen_sUnion ∅
  rw [sUnionEmpty] at h1
  apply h1
  intro t
  intro h2
  by_contra
  exact Set.not_mem_empty t h2
