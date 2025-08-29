import Game.Levels.Functions
import Game.Levels.Spaces

open Set (mem_inter_iff mem_union Subset.antisymm)
open TopologicalSpace
open STG4

World "Continuous"
Level 1
Title "Introduction to continuous functions"

Introduction "
In this world, we introduce continuous functions.
In Lean, the predicate `Continuous` asserts that a function is continuous.
Given a proposition `h : Continuous f`, you can use `h.isOpen_preimage` to prove that the preimage of an open set is open.

Let's warm up by proving that the continuous preimage of a closed set is closed.

In this level, you can use the theorem `PreimageComplement`, which you proved in the functions world,
to rewrite `f⁻¹' (Uᶜ)` as `(f⁻¹' U)ᶜ`.
"

/-- If $f \colon X \to Y$ and $U \subset Y$ is closed, then $f^{-1}(U)$ is closed. -/
Statement {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf: Continuous f) (U : Set Y) : (IsClosed U) → (IsClosed (f⁻¹' U)) := by
  Hint "As always, start with `intro h`."
  intro h
  Hint "Recall the theorem `isOpen_compl_iff`. You can rewrite the statements in terms of open sets by writing `rw [← isOpen_compl_iff]` and `rw [← isOpen_compl_iff] at {h}`."
  rw [← isOpen_compl_iff] at h
  rw [← isOpen_compl_iff]
  Hint "Remember in the functions world, we proved that the preimage of a complement is the complement of the preimage. You can use the theorem in this level, by writing `rw [← PreimageComplement]`."
  rw [← PreimageComplement]
  Hint "Now you can use `{hf}.isOpen_preimage` to finish the proof."
  apply hf.isOpen_preimage
  exact h


Conclusion "
Level completed!
"

/--
The typeclass `Continuous` is defined as follows:

```
class Continuous {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) where
  isOpen_preimage : ∀ {U : Set Y}, IsOpen U → IsOpen (f ⁻¹' U)
```

If you have hypotheses `hf : Continuous f` and `hU : isOpen U`, then `hf.isOpen_preimage U hU` is a proof of `isOpen (f ⁻¹' U)`.
-/
DefinitionDoc Continuous as "Continuous"
NewDefinition Continuous
