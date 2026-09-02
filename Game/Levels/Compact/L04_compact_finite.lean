import Game.Levels.Compact.L03_choose

open Set
namespace TTG

World "Compact"
Level 4
Title "Finite sets are compact"

Introduction "
In this level, we prove that every finite set is compact.

We will need to use the `choose!` tactic. Suppose `A : Set X` and `B : Set Y`, and you have
a hypothesis of the form `h : ∀ x ∈ A, ∃ y ∈ B, P x y`. Then `choose! g hgB hgx using h`
produces a function `g : X → Y`, together with proofs `hgB : ∀ x ∈ A, g x ∈ B` and
`hgx : ∀ x ∈ A, P x (g x)`.
In other words, it picks out a witness for each element of `A`.

Note that `g` is defined on all of `X`, not just on `A`; outside of `A` its values are
arbitrary, and the two proofs say nothing about them.

You have also been provided with the theorem `Finite.image`, which states that the image
of a finite set is finite.
"

/-- Every finite set is compact. -/
TheoremDoc TTG.finite_compact as "finite_compact" in "Compact"

/-- Show that every finite set is compact. -/
Statement finite_compact {X : Type} [TopologicalSpace X] (A : Set X) (hA : A.Finite) :
    IsCompact A := by
  Hint "As before, start with `intro F hopen hcover`."
  intro F hopen hcover
  Hint "First record, as a single statement, that every point of `{A}` lies in *some*
  member of `{F}`. Type `have key : ∀ x, x ∈ {A} → ∃ U, U ∈ {F} ∧ x ∈ U` to do this."
  have key : ∀ x, x ∈ A → ∃ U, U ∈ F ∧ x ∈ U := by
    Hint (hidden := true) "`intro x hx`, then `obtain ⟨U, hUF, hxU⟩ := {hcover} hx`."
    intro x hx
    obtain ⟨U, hUF, hxU⟩ := hcover hx
    use U
  Hint "Now turn `{key}` into an actual choice of set for each point, with
  `choose! g hgF hgx using {key}`."
  choose! g hgF hgx using key
  Hint "`g` now assigns a member of `{F}` to every point.  Which subfamily of `{F}` should
  you use?"
  Hint (hidden := true) "The sets picked out by `g`, one for each point of `{A}`: `use g '' {A}`."
  use g '' A
  Hint (hidden := true) "Split the three remaining goals with `constructor`."
  constructor
  Hint (hidden := true) "Take a member of `g '' {A}`; by `obtain` it is `g x` for some
  `x ∈ {A}`, and `{hgF}` says exactly that this lies in `{F}`."
  · intro U hU
    obtain ⟨x, hxA, rfl⟩ := hU
    exact hgF x hxA
  constructor
  Hint (hidden := true) "This is where finiteness is used: `g '' {A}` is the image of the
  finite set `{A}`, so `Finite.image g {hA}` proves it."
  · exact Finite.image g hA
  Hint (hidden := true) "Given `x ∈ {A}`, the set `g x` contains it by `{hgx}`, and `g x`
  is a member of `g '' {A}`."
  · intro x hxA
    use g x
    constructor
    use x
    exact hgx x hxA

Conclusion "
Well done!
"

/--
The image of a finite set is finite.

If `h : S.Finite` then `Finite.image f h` is a proof of `(f '' S).Finite`. This can
also be written `h.image f`.
-/
TheoremDoc Set.Finite.image as "Set.Finite.image" in "Finite"
NewTheorem Set.Finite.image
