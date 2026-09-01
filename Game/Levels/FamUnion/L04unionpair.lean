import Game.Levels.FamUnion.L03unionsubunion

open Set

namespace TTG

variable {U : Type}

World "FamUnion"
Level 4
Title "Union of a pair"

Introduction
"
In this level, you'll show that, as with intersections, family unions generalize the
unions we studied in Union World.
"

/-- For any two sets $A$ and $B$, we have $A ∪ B = ⋃₀ {A, B}$. -/
TheoremDoc TTG.sUnion_pair as "sUnion_pair" in "⋂₀⋃₀"

/-- Suppose $A$ and $B$ are sets.  Then $A \cup B = \bigcup \{A, B\}$. -/
Statement sUnion_pair (A B : Set U) : A ∪ B = ⋃₀ {A, B}:= by
  ext x
  apply Iff.intro
  intro h1
  rewrite [mem_sUnion]
  rewrite [mem_union] at h1
  rcases h1 with hA | hB
  use A
  apply And.intro
  rewrite [mem_pair]
  apply Or.inl
  rfl
  exact hA
  use B
  apply And.intro
  rewrite [mem_pair]
  right
  rfl
  exact hB
  intro h1
  rewrite [mem_union]
  rewrite [mem_sUnion] at h1
  Hint "Remember, you can use `obtain` to introduce a name for the set that is asserted to
  exist in `{h1}`."
  obtain ⟨t, ht⟩ := h1
  rewrite [mem_pair] at ht
  rcases ht.left with hA | hB
  rewrite [hA] at ht
  exact Or.inl ht.right
  rewrite [hB] at ht
  exact Or.inr ht.right
