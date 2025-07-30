import Game.Metadata

World "Functions"
Level 2
Title "Images of functions"

Introduction "
In this level, we will prove that the image of the union of two sets is equal to the union of their images.
"

open Set

/-- Show that $f(A ∪ B) = f(A) ∪ f(B)$. -/
Statement ImageUnion {X Y : Type} (A B : Set X) (f : X → Y) : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  Hint "Recall that you can use the `ext` tactic to prove that two sets are equal."
  ext y
  Hint "You can use Iff.intro to split the goal into two subgoals."
  apply Iff.intro

  Hint "As in the last level, you can use `rintro` here."
  intro h
  rcases h with ⟨x, hx, rfl⟩
  /- TODO: use rcases instead of rintro. explain it. -/
  /- rintro ⟨x, hx, rfl⟩ -/
  Hint "You can use `cases hx` to split the proof into two cases."
  cases hx
  Hint "Recall the syntax `exact ⟨x, h, rfl⟩` to finish the proof in each case."
  left
  exact ⟨x, h, rfl⟩
  right
  exact ⟨x, h, rfl⟩

  Hint "..."
  intro h
  cases h
  rcases h_1 with ⟨ x, hx, rfl ⟩
  exact ⟨x, Or.inl hx, rfl⟩
  rcases h_1 with ⟨ x, hx, rfl ⟩
  exact ⟨x, Or.inr hx, rfl⟩

Conclusion "
Level completed!
"

NewTactic rcases
NewTheorem Iff.intro Or.inl Or.inr
