import Game.Levels.Functions.L05_preimage

open Set (mem_inter_iff mem_union Subset.antisymm)
namespace TTG

World "Functions"
Level 6
Title "Preimage of union"

Introduction "
Try to solve it using what you've learned so far! Hints are available if you get stuck.
"

/-- The theorem $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
TheoremDoc TTG.preimage_union as "preimage_union" in "function"

/-- Show that $f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B)$. -/
Statement preimage_union {X Y : Type} (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∪ B) = (f ⁻¹' A) ∪ (f ⁻¹' B) := by
  Hint (hidden:=true) "Recall that the `ext` tactic can be used to prove that two sets are equal."
  ext x
  Hint (hidden:=true) "As usual, an application of `Iff.intro` will split the goal into two subgoals."
  apply Iff.intro

  intro h
  Hint (hidden:=true) "You can use `rcases {h}` to split the proof into two cases. This works because `x ∈ f ⁻¹' A` and `f x ∈ A` are the same by definition, so no rewriting is needed. (`Set.mem_preimage` can make the conversion explicit if you prefer to see it.)"
  rcases h
  Hint (hidden:=true) "Recall that `Or.inl` and `Or.inr` can be useful here."
  apply Or.inl
  exact h
  apply Or.inr
  exact h

  intro h
  Hint (hidden:=true) "You can use `rcases {h}` to split the proof into two cases. This works because `x ∈ f ⁻¹' A` and `f x ∈ A` are the same by definition, so no rewriting is needed. (`Set.mem_preimage` can make the conversion explicit if you prefer to see it.)"
  rcases h
  Hint (hidden:=true) "Recall that `Or.inl` and `Or.inr` can be useful here."
  apply Or.inl
  exact h
  apply Or.inr
  exact h

Conclusion "
Level completed!
"

DisabledTactic constructor
