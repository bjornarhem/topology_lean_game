import Game.Levels.Compact.L05_compact_union

open Set
namespace TTG

World "Compact"
Level 6
Title "Preimage of a family union"

Introduction "
This level is about how preimages interact with unions of families.  We need it for the
main theorem of this world.

Back in Functions World you showed that `f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B`.  The same is
true for a whole family of sets at once: the preimage of `⋃₀ F` is the union of the
preimages of the members of `F`.

To write \"the family of all preimages of members of `F`\" in Lean we use set-builder
notation, just as you did in Spaces World for families of complements:
```
{B | ∃ U ∈ F, B = f ⁻¹' U}
```
Read this as \"those sets `B` for which there is some `U` in `F` with `B = f ⁻¹' U`\".
"

/-- The theorem $f^{-1}(\bigcup F) = \bigcup \{f^{-1}(U) : U \in F\}$. -/
TheoremDoc TTG.preimage_sUnion as "preimage_sUnion" in "⋂₀⋃₀"

/-- Show that $f^{-1}(\bigcup F) = \bigcup \{f^{-1}(U) : U \in F\}$. -/
Statement preimage_sUnion {X Y : Type} (f : X → Y) (F : Set (Set Y)) :
    f ⁻¹' (⋃₀ F) = ⋃₀ {B | ∃ U ∈ F, B = f ⁻¹' U} := by
  Hint "As before, `ext x` and then split the `↔`."
  ext x
  apply Iff.intro

  Hint "The assumption says that `f {x}` lies in `⋃₀ {F}`, so some member of `{F}` contains
  it.  Get hold of that member with `obtain`."
  intro h
  obtain ⟨U, hUF, hfxU⟩ := h
  Hint (hidden := true) "The preimage of `{U}` is the member you want: `use f ⁻¹' {U}`."
  use f ⁻¹' U
  constructor
  Hint (hidden := true) "`use {U}` to say which member of `{F}` it is the preimage of."
  use U
  exact hfxU

  Hint "For the other direction, unpack the member of the new family and then the set of
  `{F}` it came from."
  intro h
  obtain ⟨V, hVF, hxV⟩ := h
  obtain ⟨U, hUF, rfl⟩ := hVF
  Hint (hidden := true) "`use {U}`, and then both remaining goals are assumptions you
  already have."
  use U
  constructor
  exact hUF
  exact hxV

Conclusion "
Level completed!
"
