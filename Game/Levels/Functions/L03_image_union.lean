import Game.Levels.Functions.L02_image

World "Functions"
Level 3
Title "Image of union"

Introduction "
In this level, we will prove that the image of the union of two sets is equal to the union of their images.
"

open Set

/-- The theorem $f(A ∪ B) = f(A) ∪ f(B)$. -/
TheoremDoc ImageUnion as "ImageUnion" in "function"

/-- Show that $f(A ∪ B) = f(A) ∪ f(B)$. -/
Statement ImageUnion {X Y : Type} (A B : Set X) (f : X → Y) : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  Hint "Recall that you can use the `ext` tactic to prove that two sets are equal."
  ext y
  Hint "You can apply Iff.intro to split the goal into two subgoals."
  apply Iff.intro

  Hint "As in the previous level, you can use `intro` followed by `rcases` here."
  intro h
  rcases h with ⟨x, hx, rfl⟩
  Hint "You can use `cases {hx}` to split the proof into two cases."
  cases hx
  Hint "The tactics `left` and `right` can be useful here."
  left
  Hint "Recall the syntax `exact ⟨{x}, {h}, rfl⟩` to finish the proof in each case."
  exact ⟨x, h, rfl⟩
  right
  exact ⟨x, h, rfl⟩

  Hint "The second subgoal can be solved similarly."
  intro h
  cases h
  rcases h_1 with ⟨ x, hx, rfl ⟩
  Hint "The theorems `Or.inl` and `Or.inr` can be useful here."
  exact ⟨x, Or.inl hx, rfl⟩
  rcases h_1 with ⟨ x, hx, rfl ⟩
  exact ⟨x, Or.inr hx, rfl⟩

Conclusion "
Level completed!
"
