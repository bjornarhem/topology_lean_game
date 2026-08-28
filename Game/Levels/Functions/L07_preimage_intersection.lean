import Game.Levels.Functions.L06_preimage_union

open Set (mem_inter_iff mem_union Subset.antisymm)
namespace TTG

World "Functions"
Level 7
Title "Preimage of intersection"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

/-- The theorem $f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B)$. -/
TheoremDoc TTG.preimage_intersection as "preimage_intersection" in "function"

/-- Show that $f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B)$. -/
Statement preimage_intersection {X Y : Type} (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = (f ⁻¹' A) ∩ (f ⁻¹' B) := by
  ext x
  apply Iff.intro

  intro h
  apply And.intro
  exact h.left
  exact h.right

  intro h
  apply And.intro
  exact h.left
  exact h.right


Conclusion "
Level completed!
"

DisabledTactic constructor
