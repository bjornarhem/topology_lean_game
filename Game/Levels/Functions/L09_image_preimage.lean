import Game.Levels.Functions.L08_preimage_complement

open Set (mem_inter_iff mem_union Subset.antisymm)
open STG4

World "Functions"
Level 9
Title "Image of preimage"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

/-- The theorem $f(f^{-1}(A)) \subseteq A $. -/
TheoremDoc ImagePreimage as "ImagePreimage" in "function"

/-- Show that $f(f^{-1}(A)) \subseteq A $. -/
Statement ImagePreimage {X Y : Type} (A : Set Y) (f : X → Y) : f '' (f ⁻¹' (A)) ⊆ A  := by
  intro y
  intro h
  obtain ⟨x, hx, rfl⟩ := h
  exact hx


Conclusion "
Level completed!
"
