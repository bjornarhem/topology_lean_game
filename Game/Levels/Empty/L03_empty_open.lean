import Game.Levels.Empty.L02_empty_union

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter mem_setOf)
open TopologicalSpace
open STG4

World "Empty"
Level 3
Title "The empty set is open"

Introduction "
In this level, show that the empty set is open in any topological space.

In this level, you will have to use the `isOpen_sUnion` property of topological spaces.
The `isOpen_sUnion` property states that the union over any collection of open sets is open.
Explicitly, `TopologicalSpace.isOpen_sUnion` is defined as
```
∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```
You can look up the definition of `TopologicalSpace` in the right column if you want to read more.
"

/-- Let $X$ be a topological space. Then $\emptyset \subseteq X$ is open. -/
Statement {X : Type} [h : TopologicalSpace X] : IsOpen (∅ : Set X) := by
  Hint (hidden := true) "Try using `h.isOpen_sUnion` on the empty collection."
  have h1 := h.isOpen_sUnion ∅
  Hint "You can use the theorem `sUnionEmpty` from the previous level."
  rw [sUnionEmpty] at h1
  apply h1
  intro t
  intro h2
  by_contra
  exact Set.not_mem_empty t h2
