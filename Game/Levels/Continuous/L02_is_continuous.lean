import Game.Levels.Continuous.L01_continuous

World "Continuous"
Level 2
Title "Composition of continuous functions"

Introduction "
TODO: explain
talk about continuous_def
"

open TopologicalSpace Set
namespace continuous

/-- TODO: write statement -/
Statement {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf: Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- TODO: add hints
  rw [continuous_def]
  intro U hU
  rw [PreimageComposition]
  -- TODO: add hint for using result here
  apply hf.isOpen_preimage
  apply hg.isOpen_preimage
  exact hU


Conclusion "
Level completed!
"

-- TODO: theoremdoc
NewTheorem continuous_def
