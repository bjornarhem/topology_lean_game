import Game.Levels.Compact.L06_preimage_sUnion

open Set
namespace TTG

World "Compact"
Level 7
Title "Continuous image of a compact set"

Introduction "
This is the main theorem of this world: the continuous image of a compact set is compact.

It is the hardest level in this world, but by now you have all the tools you need.

Some general tips for this level:
* If you get stuck, try doing the proof with pen and paper first.  The Lean proof follows
  the mathematical one closely.
* The theorem from the previous level, and several from Functions World, will do a lot of
  the work for you.
* You can use the `have` tactic to prove a statement over multiple lines. Look in the tactic documentation for how to do this.
* Every step of this level has a hidden hint, so you can always ask for more help.

Good luck!
"

/-- The continuous image of a compact set is compact. -/
TheoremDoc TTG.compact_image as "compact_image" in "Compact"

/-- Show that the continuous image of a compact set is compact. -/
Statement compact_image {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) (s : Set X) (hs : IsCompact s) : IsCompact (f '' s) := by
  Hint (hidden := true) "Start with `intro F hopen hcover`."
  intro F hopen hcover
  Hint (hidden := true) "Step 1.  Record that the pulled-back family `preimage {f} '' {F}` consists of
  open sets.  Use `have hpullopen : ∀ V ∈ preimage {f} '' {F}, IsOpen V`"
  Hint (hidden := true) "After `intro V hV`, use `obtain ⟨U, hUF, rfl⟩ := hV` to see that
  `V` is `f ⁻¹' U` for some `U ∈ {F}`, then apply continuity of `{f}`."
  have hpullopen : ∀ V ∈ preimage f '' F, IsOpen V := by
    intro V hV
    obtain ⟨U, hUF, rfl⟩ := hV
    exact hf.isOpen_preimage U (hopen U hUF)
  Hint (hidden := true) "Still step 1: record that the pulled-back family covers `s`.  This is where the
  previous level pays off."
  Hint (hidden := true) "Rewrite with `preimage_sUnion` backwards, so that the goal becomes
  `s ⊆ f ⁻¹' (⋃₀ {F})`.  Then chain `preimage_image` and `preimage_subset` with
  `Subset.trans`."
  have hpullcover : s ⊆ ⋃₀ (preimage f '' F) := by
    rewrite [← preimage_sUnion]
    apply Subset.trans (preimage_image s f)
    apply preimage_subset
    exact hcover
  Hint (hidden := true) "Step 2.  Now apply compactness of `s` to the pulled-back family."
  Hint (hidden := true) "`obtain ⟨G, hGsub, hGfin, hGcov⟩ := {hs} _ {hpullopen} {hpullcover}`
  — you can write `_` for the family, since Lean can work out which one you mean from the
  two hypotheses."
  obtain ⟨G, hGsub, hGfin, hGcov⟩ := hs _ hpullopen hpullcover
  Hint (hidden := true) "Step 3.  Every member of `{G}` is the preimage of some member of `{F}`.  State that
  as a single `have`, then feed it to `choose!`."
  Hint (hidden := true) "`have key : ∀ V, V ∈ {G} → ∃ U, U ∈ {F} ∧ f ⁻¹' U = V`, proved with
  `intro`, `obtain` and `use`."
  have key : ∀ V, V ∈ G → ∃ U, U ∈ F ∧ f ⁻¹' U = V := by
    intro V hV
    obtain ⟨U, hUF, hUV⟩ := hGsub hV
    use U
  Hint (hidden := true) "`choose! g hgF hgeq using {key}` gives you the choice of a member
  of `{F}` for each member of `{G}`."
  choose! g hgF hgeq using key
  Hint (hidden := true) "Which finite subfamily of `{F}` covers `f '' s`?"
  Hint (hidden := true) "The sets chosen by `g`: `use g '' {G}`."
  use g '' G
  constructor
  Hint (hidden := true) "A member of `g '' {G}` is `g V` for some `V ∈ {G}`, and `{hgF}`
  says that lies in `{F}`."
  · intro U hU
    obtain ⟨V, hVG, rfl⟩ := hU
    exact hgF V hVG
  constructor
  Hint (hidden := true) "`g '' {G}` is the image of the finite set `{G}`, so use
  `Finite.image`."
  · exact Finite.image g hGfin
  Hint (hidden := true) "Take `y ∈ f '' s`, so `y = f x` with `x ∈ s`.  Then `{hGcov}` puts
  `x` in some `V ∈ {G}`, and `{hgeq}` says `f ⁻¹' (g V) = V`, so `f x ∈ g V`."
  · intro y hy
    obtain ⟨x, hxs, rfl⟩ := hy
    obtain ⟨V, hVG, hxV⟩ := hGcov hxs
    use g V
    constructor
    use V
    have h2 : f ⁻¹' (g V) = V := hgeq V hVG
    rewrite [← h2] at hxV
    exact hxV

Conclusion "
Congratulations!
"
