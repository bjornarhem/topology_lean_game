import Game.Levels.Functions.L09_image_preimage

open Set
namespace TTG

World "Functions"
Level 10
Title "Preimage of image"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

/-- The theorem $A \subseteq f^{-1}(f(A))$. -/
TheoremDoc TTG.preimage_image as "preimage_image" in "function"

/-- Show that $A \subseteq f^{-1}(f(A))$. -/
Statement preimage_image {X Y : Type} (A : Set X) (f : X → Y) : A ⊆ f ⁻¹' (f '' A)  := by
  intro y
  intro h
  exact ⟨y, h, rfl⟩


Conclusion "
Level completed!
"
