import Game.Levels.Functions.L08_preimage_complement

open Set (mem_inter_iff mem_union Subset.antisymm)
namespace TTG

World "Functions"
Level 9
Title "Image of preimage"

Introduction "
In this level, there's no hints. Try to solve it using what you've learned so far!
"

/-- The theorem $f(f^{-1}(A)) \subseteq A $. -/
TheoremDoc TTG.image_preimage as "image_preimage" in "function"

/-- Show that $f(f^{-1}(A)) \subseteq A $. -/
Statement image_preimage {X Y : Type} (A : Set Y) (f : X → Y) : f '' (f ⁻¹' (A)) ⊆ A  := by
  intro y
  intro h
  obtain ⟨x, hx, rfl⟩ := h
  exact hx


Conclusion "
Level completed!
"
