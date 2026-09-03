import Game.Levels.Empty.L02_empty_union

open Set
namespace TTG

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
Statement {X : Type} [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  Hint "You can use the theorem `sUnion_empty` from the previous level to rewrite `∅` as
  the union of the empty family."
  Hint (hidden := true) "Try `rw [← sUnion_empty]`."
  rw [← sUnion_empty]
  Hint (hidden := true) "Now the axiom `isOpen_sUnion` applies."
  apply isOpen_sUnion
  intro t
  intro h2
  by_contra
  exact Set.notMem_empty t h2
