import Game.Levels.Functions.L07_preimage_intersection

open Set
namespace TTG

World "Functions"
Level 8
Title "Preimage of complement"

Introduction "
In this level, we prove that $f^{-1}(A^c) = f^{-1}(A)^c$,
where $A^c$ is the complement of $A$ in the universe of discourse.
In Lean, this is denoted `Aᶜ` or `Set.compl A`, and can be written `\\^c`.
Recall that `x ∈ Aᶜ ↔ x ∉ A`.
"

/--
The theorem $f^{-1}(A^c) = f^{-1}(A)^c$
-/
TheoremDoc TTG.preimage_compl as "preimage_compl" in "function"

/-- Show that $f^{-1}(A^c) = f^{-1}(A)^c$. -/
Statement preimage_compl {X Y : Type} (A : Set Y) (f : X → Y) : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ := by
  Hint "In this level, it can be useful to use `rewrite [mem_compl_iff]` or `rewrite [mem_compl_iff] at h` to rewrite at statement `a ∈ Sᶜ` to `a ∉ S`."
  Hint "Another useful technique is to use `by_contra` to do a proof by contradiction."
  ext y
  apply Iff.intro
  intro h
  rewrite [mem_compl_iff]
  Hint (hidden:=true) "`{f} {y} ∈ {A}ᶜ` is equivalent to `{f} {y} ∉ {A}`, which in turn is equivalent to `({f} {y} ∈ {A}) → False`. Do you see how we can get a proof by contradiction?"
  by_contra h2
  exact h h2

  intro h
  rewrite [mem_compl_iff] at h
  Hint (hidden:=true) "You can't use `rewrite [mem_compl_iff]` directly here, because the goal is not of the correct form. Rewriting with `Set.mem_preimage` gives you the desired form."
  rewrite [Set.mem_preimage]
  rewrite [mem_compl_iff]
  Hint (hidden:=true) "`{f} {y} ∈ {A}ᶜ` is equivalent to `{f} {y} ∉ {A}`, which in turn is equivalent to `({f} {y} ∈ {A}) → False`. Do you see how we can get a proof by contradiction?"
  by_contra h2
  exact h h2

Conclusion "
Level completed!
"

DisabledTactic constructor
