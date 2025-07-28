import Game.Metadata

World "Functions"
Level 2
Title "Images of functions"

Introduction "
If $f \\colon X \\to Y$ and $A \\in X$, then the image of $A$ under $f$ is the set
$f(A) = \\{ f(x) \\mid x \\in A \\}$. In lean, this is denoted `f '' A` or `image f A`.
"

open Set

/-- Show that $f(A ∪ B) = f(A) ∪ f(B)$. -/
Statement {X Y : Type} (A B : Set X) (f : X → Y) : f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  /- TODO: rewrite to use more known tactics (if needed), and give more hints. -/
  Hint "You can use the `ext` tactic to prove that two sets are equal."
  ext y
  Hint "To show that $y$ is in the left-hand side, you need to show that $y$ is in $f(A ∪ B)$."
  apply Iff.intro
  . rintro ⟨x, hx, rfl⟩
    Hint "You can use `cases` to split the proof into two cases."
    cases hx
    . left
      exact ⟨x, h, rfl⟩
    . right
      exact ⟨x, h, rfl⟩
  rintro h
  cases h
  . rcases h_1 with ⟨ x, hx, rfl ⟩
    exact ⟨x, Or.inl hx, rfl⟩
  . rcases h_1 with ⟨ x, hx, rfl ⟩
    exact ⟨x, Or.inr hx, rfl⟩
  -- . rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
  --   . exact ⟨x, Or.inl hx, rfl⟩
  --   . exact ⟨x, Or.inr hx, rfl⟩

Conclusion "
Level completed!
"

NewDefinition Set.image
NewTactic cases rintro apply ext exact right left rcases
NewTheorem Iff.intro Or.inl Or.inr
