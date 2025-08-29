import Game.Levels.Spaces.L01_spaces

open Set (mem_inter_iff mem_union Subset.antisymm)
open TopologicalSpace
open STG4

World "Spaces"
Level 3
Title "The empty set"

Introduction "
In this level, we introduce the empty set and show that it's open in any topological space.
"

-- TODO: introduce level showing that the empty union is the empty set

/-- Let $X$ be a topological space. Then $\emptyset \subseteq X$ is open. -/
Statement {X : Type} [h : TopologicalSpace X] : IsOpen (∅ : Set X) := by
  have h1 := h.isOpen_sUnion ∅
  rw [Set.sUnion_empty] at h1
  apply h1
  intro t
  intro h2
  by_contra
  exact Set.not_mem_empty t h2
  -- TODO: think about if this is the best way.

-- TODO: define emptyset here
