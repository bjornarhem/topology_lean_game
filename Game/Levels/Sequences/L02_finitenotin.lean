import Game.Levels.Sequences.L01_uniquelimit

open Set
namespace TTG

World "Sequences"
Level 2
Title "Outside the Neighbourhood of the Limit"

Introduction
"
Here you will prove an auxiliary lemma that will help you in the next level.
"

/--
If a sequence $(s_n)_n$ converges to $x$, then for any open neighbourhood $U$ of $x$,
all but finitely many elements belong of $(s_n)_n$ to $U$.
-/
TheoremDoc TTG.ConvergesTo.finite_setOf_notMem as "ConvergesTo.finite_setOf_notMem" in "topology"

TheoremTab "Finite"

/-- For any natural number `N`, `Set.finite_le_nat N` is a proof that the set
`{n | n ≤ N}` of natural numbers is finite. -/
TheoremDoc Set.finite_le_nat as "Set.finite_le_nat" in "Finite"

/-- If `h : m < n`, then `le_of_lt h` is a proof of `m ≤ n`. -/
TheoremDoc le_of_lt as "le_of_lt" in "ℕ"

NewTheorem Set.finite_le_nat le_of_lt

Statement ConvergesTo.finite_setOf_notMem {X : Type} [TopologicalSpace X] (s : ℕ → X) (t : X) (hst : ConvergesTo s t) :
    ∀ U, IsOpen U → t ∈ U → Set.Finite {n | s n ∉ U} := by
  intro U Uopen tinU
  Hint "Apply {hst} to {U} and extract a suitable {U}."
  obtain ⟨N, hN⟩ := hst U Uopen tinU
  Hint "Try to guess the next step while keeping in mind that eventually you
  will have to use `Set.finite_le_nat`."
  Hint (hidden := true) "Write `apply Finite.subset (s := \{n | n ≤ {N}})`."
  apply Finite.subset (s := {n | n ≤ N})
  · Hint "Write `Set.finite_le_nat N`."
    exact Set.finite_le_nat N
  · intro n hn
    rw [mem_setOf] at *
    Hint "Proceed by reductio ad absurdum. Applying `push_neg` to `¬n ≤ N`
    changes it into `N < n`."
    by_contra hnN; push_neg at hnN
    Hint (hidden := true) "Use `le_of_lt`."
    have hnN' := le_of_lt hnN
    exact hn (hN n hnN')
