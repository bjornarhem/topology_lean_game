import Game.Levels.Compact.L07_compact_image

open Set
namespace TTG

World "Compact"
Level 8
Title "Case closed"

Introduction "
For the final level of this world, we prove that a closed subset of a compact set is compact.

As in the previous level, we recommend that you solve the problem with pen and paper first.

It can be useful to recall that you can take intersections and unions of familes
of sets.  In particular, if you have a family of sets `F` and another set `B`,
then `F ∪ {B}` denotes the family consisting of all members of `F` together with
`B`.
"

/-- A closed subset of a compact set is compact. -/
TheoremDoc TTG.compact_closed_subset as "compact_closed_subset" in "Compact"

/-- A closed subset of a compact set is compact. -/
Statement compact_closed_subset {X : Type} [TopologicalSpace X] (s A : Set X)
    (hA : IsClosed A) (hAs : A ⊆ s) (hs : IsCompact s) : IsCompact A := by
  Hint (hidden := true) "As always, start with `intro F hopen hcover`."
  intro F hopen hcover
  Hint (hidden := true) "First record that every member of `{F} ∪ \{{A}ᶜ}` is open.  Use
  `have hopen' : ∀ U ∈ {F} ∪ \{{A}ᶜ}, IsOpen U`"
  Hint (hidden := true) "Inside that proof, `rcases` the assumption `U ∈ {F} ∪ \{{A}ᶜ}` into
  two cases.  In the second case the assumption *is* the equation `U = {A}ᶜ`, so you can
  `rewrite` with it, and then `isOpen_compl_iff` finishes."
  have hopen' : ∀ U ∈ F ∪ {Aᶜ}, IsOpen U := by
    intro U hU
    rcases hU with hU | hU
    exact hopen U hU
    rw [hU, isOpen_compl_iff]
    exact hA
  Hint (hidden := true) "Now record that `{F} ∪ \{{A}ᶜ}` covers all of `s`.  Given `x ∈ s`,
  split on whether `x ∈ {A}` with `by_cases`."
  have hcover' : s ⊆ ⋃₀ (F ∪ {Aᶜ}) := by
    intro x hx
    by_cases hxA : x ∈ A
    obtain ⟨U, hUF, hxU⟩ := hcover hxA
    use U
    constructor
    left
    exact hUF
    exact hxU
    use Aᶜ
    constructor
    right
    rfl
    exact hxA
  Hint (hidden := true) "Apply compactness of `s` to the family `{F} ∪ \{{A}ᶜ}`."
  obtain ⟨G, hGsub, hGfin, hGcov⟩ := hs _ hopen' hcover'
  Hint "You now have a finite `{G} ⊆ {F} ∪ \{{A}ᶜ}` covering `s`.  How do you get from it a
  finite subfamily of `{F}` alone?"
  Hint (hidden := true) "Intersect with `{F}`: `use {G} ∩ {F}`."
  use G ∩ F
  Hint (hidden := true) "A member of `{G} ∩ {F}` is in `{F}` by `.right`."
  constructor
  intro U hU
  exact hU.right
  constructor
  Hint (hidden := true) "You proved exactly this in the first level of this world:
  `inter_finite {G} {F} {hGfin}`."
  exact inter_finite G F hGfin
  Hint (hidden := true) "Finally, take `x ∈ {A}`.  Since `{A} ⊆ s`, the family `{G}` covers
  it, giving some `U ∈ {G}` with `x ∈ U`.  You must show that this `U` also lies in `{F}` —
  and it does, because `U = {A}ᶜ` would contradict `x ∈ {A}`."
  intro x hxA
  obtain ⟨U, hUG, hxU⟩ := hGcov (hAs hxA)
  use U
  constructor
  constructor
  exact hUG
  rcases hGsub hUG with hUF | hUc
  exact hUF
  rw [hUc] at hxU
  by_contra
  exact hxU hxA
  exact hxU

Conclusion "
Congratulations! You have completed the Compact World.
"
