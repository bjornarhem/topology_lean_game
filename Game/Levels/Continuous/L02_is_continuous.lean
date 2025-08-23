import Game.Levels.Continuous.L01_continuous

World "Continuous"
Level 2
Title "Composition of continuous functions"

Introduction "
In this level, we prove that the composition of continuous functions is continuous.

We introduce the theorem `continuous_def`, which states that a function is continuous if and only if the preimage of every open set is open.
"

open TopologicalSpace Set
namespace continuous

/-- The composition of continuous functions is continuous. -/
Statement {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf: Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  Hint "In this level, you can use the theorem `continuous_def`, which states that a function is continuous if and only if the preimage of every open set is open. Try using `rw [continuous_def]`."
  rw [continuous_def]
  intro U hU
  Hint "In this level, you can use the theorem `PreimageComposition`, which you proved in the functions world."
  rw [PreimageComposition]
  Hint "Again, you can use `{hf}.isOpen_preimage` and `{hg}.isOpen_preimage` to finish the proof."
  apply hf.isOpen_preimage
  apply hg.isOpen_preimage
  exact hU


Conclusion "
Level completed!
"

/-- A function is continuous if and only if the preimage of every open set is open. -/
TheoremDoc continuous_def as "continuous_def" in "continuous"

NewTheorem continuous_def
