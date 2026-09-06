import Game.Levels.Continuous.L02_is_continuous

open Set
namespace TTG

World "Continuous"
Level 3
Title "Closing time"

Introduction "
In the first level of this world, you showed that if a function `f` is
continuous, then the preimage of a closed set under `f` is closed.  In this
level we prove the converse statement: if the preimage of every closed set under
`f` is closed, then `f` is continuous.
"

/-- If $f^{-1}(U)$ is closed for every closed $U$, then $f$ is continuous. -/
Statement {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (h : ∀ U : Set Y, IsClosed U → IsClosed (f ⁻¹' U)) : Continuous f := by
  Hint "As in the previous level, start with `rw [continuous_def]` and then introduce an
  open set."
  rw [continuous_def]
  intro U hU
  Hint (hidden:=true) "What happens if you write `have hc := {h} {U}ᶜ`?"
  have hc := h Uᶜ
  Hint (hidden:=true) "The theorem `preimage_compl` from the Functions world can be useful in this level."
  Hint (hidden:=true) "In the right column, you can also look up the theorem `isOpen_compl_iff` (in the `topology` tab), as well as the theorem `compl_compl` (in the `ᶜ` tab)."
  have huc : IsClosed Uᶜ := by
    rw [← isOpen_compl_iff]
    rw [compl_compl]
    exact hU
  have hfuc := hc huc
  rw [preimage_compl] at hfuc
  rw [← isOpen_compl_iff] at hfuc
  rw [compl_compl] at hfuc
  exact hfuc

Conclusion "
Great job!
"
