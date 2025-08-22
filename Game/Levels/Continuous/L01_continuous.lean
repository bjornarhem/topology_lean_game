import Game.Levels.Functions
import Game.Levels.Spaces

World "Continuous"
Level 1
Title "Introduction to continuous functions"

Introduction "
TODO: explain
remember: explain hf.isOpen_preimage
"

namespace continuous

/-- If $f \\colon X \\to Y$ and $U \\subset Y$ is closed, then $f^{-1}(U)$ is closed. -/
Statement ContinuousPreimageClosed {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (hf: Continuous f) (U : Set Y) : (IsClosed U) → (IsClosed (f⁻¹' U)) := by
  intro h
  rw [← isOpen_compl_iff] at h
  rw [← isOpen_compl_iff]
  -- TODO: add hint that you can use PreimageComplement
  rw [← PreimageComplement]
  -- TODO: explain hf.isOpen_preimage
  apply hf.isOpen_preimage
  exact h


Conclusion "
Level completed!
"

/--
TODO
-/
DefinitionDoc Continuous as "Continuous"
NewDefinition Continuous
