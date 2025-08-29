import Game.Levels.Functions.L05_preimage

open Set (mem_inter_iff mem_union Subset.antisymm)
open STG4

World "Functions"
Level 6
Title "Preimage of union"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

/-- The theorem $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
TheoremDoc PreimageUnion as "PreimageUnion" in "function"

/-- Show that $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
Statement PreimageUnion {X Y : Type} (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∪ B) = (f ⁻¹' A) ∪ (f ⁻¹' B) := by
  ext x
  apply Iff.intro

  intro h
  rcases h
  apply Or.inl
  exact h
  apply Or.inr
  exact h

  intro h
  rcases h
  apply Or.inl
  exact h
  apply Or.inr
  exact h

Conclusion "
Level completed!
"
