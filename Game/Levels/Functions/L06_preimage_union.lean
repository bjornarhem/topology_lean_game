import Game.Levels.Functions.L05_preimage

World "Functions"
Level 6
Title "Preimage of union"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

open Set

/-- The theorem $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
TheoremDoc PreimageUnion as "PreimageUnion" in "function"

/-- Show that $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
Statement PreimageUnion {X Y : Type} (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∪ B) = (f ⁻¹' A) ∪ (f ⁻¹' B) := by
  ext x
  apply Iff.intro

  intro h
  cases h
  apply Or.inl
  exact h_1
  apply Or.inr
  exact h_1

  intro h
  cases h
  apply Or.inl
  exact h_1
  apply Or.inr
  exact h_1

Conclusion "
Level completed!
"
