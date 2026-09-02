import Game.Levels.Compact.L04_compact_finite

open Set
namespace TTG

World "Compact"
Level 5
Title "Union of two compact sets"

Introduction "
Now let's show that if `s` and `t` are compact, then so is `s ∪ t`.

You have been provided with another theorem, `Finite.union`, which states that
the union of two finite sets is finite.
"

/-- The union of two compact sets is compact. -/
TheoremDoc TTG.compact_union as "compact_union" in "Compact"

/-- Show that the union of two compact sets is compact. -/
Statement compact_union {X : Type} [TopologicalSpace X] (s t : Set X)
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  Hint "Start with `intro F hopen hcover`."
  intro F hopen hcover
  Hint "Before you can use `{hs}`, you need to know that `{F}` covers `s` on its own.
  Use `have` to record that."
  Hint (hidden := true) "`have hsF : s ⊆ ⋃₀ {F}`, then `intro x hx`, `apply {hcover}`,
  and finish with `left`."
  have hsF : s ⊆ ⋃₀ F := by
    intro x hx
    apply hcover
    left
    exact hx
  Hint (hidden := true) "Now the same for `t`, using `right` instead of `left`."
  have htF : t ⊆ ⋃₀ F := by
    intro x hx
    apply hcover
    right
    exact hx
  Hint "Now apply compactness of `s` and of `t` to get two finite subfamilies."
  Hint (hidden := true) "`obtain ⟨G, hGF, hGfin, hGcov⟩ := {hs} {F} {hopen} {hsF}`, and
  similarly for `t`."
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hs F hopen hsF
  obtain ⟨H, hHF, hHfin, hHcov⟩ := ht F hopen htF
  Hint "Which subfamily covers all of `s ∪ t`?"
  Hint (hidden := true) "Use the union of the two: `use {G} ∪ {H}`."
  use G ∪ H
  constructor
  Hint (hidden := true) "A member of `{G} ∪ {H}` is in `{G}` or in `{H}`, so `rcases` it
  and use `{hGF}` or `{hHF}`."
  · intro U hU
    rcases hU with hU | hU
    exact hGF hU
    exact hHF hU
  constructor
  Hint (hidden := true) "This is the new theorem: `Finite.union {hGfin} {hHfin}`."
  · exact Finite.union hGfin hHfin
  Hint (hidden := true) "Take `x ∈ s ∪ t` and `rcases` it.  In each case the corresponding
  subfamily already covers that part."
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨U, hUG, hxU⟩ := hGcov hx
      use U
      constructor
      left
      exact hUG
      exact hxU
    · obtain ⟨U, hUH, hxU⟩ := hHcov hx
      use U
      constructor
      right
      exact hUH
      exact hxU

Conclusion "
Level completed!
"

/--
The union of two finite sets is finite.

If `h1 : S.Finite` and `h2 : T.Finite`, then `Finite.union h1 h2` is a proof that
`(S ∪ T).Finite`.  This can also be written `h1.union h2`.
-/
TheoremDoc Set.Finite.union as "Set.Finite.union" in "Finite"
NewTheorem Set.Finite.union
