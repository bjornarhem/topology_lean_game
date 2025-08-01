import Game.Metadata

World "Functions"
Level 9
Title "Image of preimage"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

open Set

namespace function

/-- Show that $f(f^{-1}(A)) \subseteq A $. -/
Statement ImagePreimage {X Y : Type} (A : Set Y) (f : X → Y) : f '' (f ⁻¹' (A)) ⊆ A  := by
  intro y
  intro h
  rcases h with ⟨x, hx, rfl⟩
  exact hx


Conclusion "
Level completed!
"
