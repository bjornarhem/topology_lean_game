import Game.Levels.Functions.L11_composition

World "Functions"
Level 12
Title "Preimage of composition"

Introduction "
The final level in this world!
"

open Set

/-- The theorem $(g \circ f)^{-1}(A) = f^{-1}(g^{-1}(A))$. -/
TheoremDoc PreimageComposition as "PreimageComposition" in "function"

/-- Show that $(g \circ f)^{-1}(A) = f^{-1}(g^{-1}(A))$. -/
Statement PreimageComposition {X Y : Type} (A : Set Z) (f : X → Y) (g : Y → Z) : (g ∘ f) ⁻¹' (A) = f ⁻¹' (g ⁻¹' A)  := by
  ext x
  apply Iff.intro

  intro h
  rewrite [Set.mem_preimage]
  rewrite [Set.mem_preimage]
  rewrite [Set.mem_preimage] at h
  exact h

  intro h
  rewrite [Set.mem_preimage]
  rewrite [Set.mem_preimage] at h
  rewrite [Set.mem_preimage] at h
  exact h


Conclusion "
Level completed!
"
