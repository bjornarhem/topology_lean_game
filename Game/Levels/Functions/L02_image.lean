import Game.Metadata

World "Functions"
Level 2
Title "Images of functions"

Introduction "
If $f \\colon X \\to Y$ and $A \\in X$, then the image of $A$ under $f$ is the set
$f(A) = \\{ f(x) \\mid x \\in A \\}$. In lean, this is denoted `f '' A` or `image f A`.
"

open Set

/-- Show that if A ⊆ B, then $f(A) ⊆ f(B)$. -/
Statement {X Y : Type} (A B : Set X) (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  /- TODO: let the user reference this theorem later -/
  Hint "Let's star by choosing an element `y` in the left-hand side, using `intro`."
  intro y
  Hint "TODO: explain rintro for working with images."
  rintro ⟨x, hxA, rfl⟩
  Hint "TODO: recall the keyword `have`"
  have hxB : x ∈ B := h hxA
  Hint "TODO: give hint for using `exact`"
  exact ⟨x, hxB, rfl⟩


Conclusion "
Level completed!
"

NewDefinition Set.image
NewTactic intro
