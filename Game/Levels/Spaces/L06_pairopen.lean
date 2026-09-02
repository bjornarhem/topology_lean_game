import Game.Levels.Spaces.L05_interclosed

open TopologicalSpace

namespace TTG

World "Spaces"
Level 6
Title "Union of Two Open Sets"

Introduction "
In this level, we are going to prove that the union of two open sets is open.
Since this arises trivially from the axioms of a topological space,
the real difficulty is in reconciling the notions of
pairwise unions and family unions.
Fortunately, `sUnion_pair` does most of the heavy lifting.
"

/-- If $U$ and $V$ are open sets, then $U ∪ V$ is also open. -/
TheoremDoc TTG.IsOpen.union as "IsOpen.union" in "topology"

/-- If $U$ and $V$ are open sets, $U ∪ V$ is also open. -/
Statement IsOpen.union {X : Type} [h : TopologicalSpace X] (U V : Set X) : IsOpen U → IsOpen V → IsOpen (U ∪ V) := by
  intro hU hV
  Hint "We want to be able to use `isOpen_sUnion` on the set `\{U, V}`. To satisfy the conditions of this theorem,
  first prove the intermediary result: `∀ A ∈ \{U, V}, IsOpen A`"
  have hUV : ∀ A ∈ {U, V}, IsOpen A := by
    Hint (hidden := true) "`rintro A (rfl | rfl)` will automatically introduce `A`
    and split the statement `A ∈ \{U, V} into two cases."
    rintro A (rfl | rfl)
    · exact hU
    · exact hV
  Hint (hidden := true) "Make use of `isOpen_sUnion` and `sUnion_pair`."
  have := isOpen_sUnion hUV
  rwa [←sUnion_pair] at this
