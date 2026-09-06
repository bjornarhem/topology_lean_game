import Game.Levels.Compact
import Game.Levels.Hausdorff

open Set
namespace TTG

World "Sequences"
Level 1
Title "Uniqueness of Limits in Hausdorff Spaces"

Introduction
"
In this level, we introduce the notion of a sequence within the context of a topological space.
It differs slightly from the notion you may have already seen in your Analysis courses,
so it is worthwhile to pause and make sure it makes sense that they do not conflict.

You are asked to prove that the limit of a sequence is unique if the space is Hausdorff.
For that, you consider two limits $x$ and $y$ and prove they are equal.

We introduce only the facts about the implementation of the natural integers that are relevant to this game.
The operands `≤` (typed \"le\" or \"<=\") and `≥` (typed \"ge\" or \">=\")
have their natural meaning. The propositions `m < n` and ` n > m` are definitionally equivalent,
as well as `m ≤ n` and `n ≥ m`, but Lean usually prefers to use `<` and `≤`.

The maximum of two natural integers is typed as `max m n`, and the theorems that state
`m ≤ max m n` and `n ≤ max m n` are called `le_max_left` and `le_max_right` respectively.

Write out you proof by pen before attempting to type it out in Lean.
"

/--A sequence $(s_n)_n$ converges to $x$ if for any $U$ an open neighbourhood of $x$.
there exists $N ∈ ℕ$ such that $∀ n ≥ N, s_n ∈ U$.
-/
DefinitionDoc ConvergesTo as "ConvergesTo"

/-- For natural numbers `m` and `n`, `max m n` is the larger of the two.
It satisfies `m ≤ max m n` and `n ≤ max m n`, proven by `le_max_left` and `le_max_right`. -/
DefinitionDoc max as "max"

NewDefinition ConvergesTo max

def ConvergesTo {X : Type} [TopologicalSpace X] (s : ℕ → X) (x : X) :=
  ∀ U, IsOpen U → x ∈ U → ∃ N, ∀ n ≥ N, s n ∈ U

/--
If $X$ is a Hausdorff space and $(s_n)_n$ is a sequence of points in $X$ that converges
to two points $x$ and $y$ in $X$, then $x=y$.
-/
Statement {X : Type} [TopologicalSpace X] [T2 : T2Space X] (s : ℕ → X) (x y : X) (hx : ConvergesTo s x) (hy: ConvergesTo s y) : x = y := by
  Hint "Use reductio ad absurdum."
  by_contra xney
  Hint (hidden := true) "Don't forget to use `push_neg` after `by_contra`."
  push_neg at xney
  Hint "Use the Hausdorff condition to separate {x} and {y}."
  Hint (hidden := true) "`{T2}.t2 {x} {y} {xney}` is a proof for `∃ u v, IsOpen u ∧ IsOpen v ∧ {x} ∈ u ∧ {y} ∈ v ∧ u ∩ v = ∅`."
  obtain ⟨U, V, Uopen, Vopen, xinU, yinV, UVdisj⟩ := T2.t2 x y xney
  Hint "Extract two natural integers `Nx` and `Ny` from each respective convergence hypothesis."
  obtain ⟨Nx, hNx⟩ := hx U Uopen xinU
  obtain ⟨Ny, hNy⟩ := hy V Vopen yinV
  Hint "Prove that `{s} (max {Nx} {Ny}) ∈ {U} ∩ {V}` and show this contraditcs `{UVdisj}`"
  have : s (max Nx Ny) ∈ U ∩ V := by
    constructor
    · apply hNx; apply le_max_left
    · apply hNy; apply le_max_right
  rw [UVdisj] at this
  exact (Set.notMem_empty (s (max Nx Ny))) this

TheoremTab "ℕ"

/-- For any natural numbers `m` and `n`, `le_max_left m n` is a proof of `m ≤ max m n`. -/
TheoremDoc le_max_left as "le_max_left" in "ℕ"

/-- For any natural numbers `m` and `n`, `le_max_right m n` is a proof of `n ≤ max m n`. -/
TheoremDoc le_max_right as "le_max_right" in "ℕ"

NewTheorem le_max_left le_max_right
