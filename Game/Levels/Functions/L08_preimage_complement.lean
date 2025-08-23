import Game.Levels.Functions.L07_preimage_intersection

World "Functions"
Level 8
Title "Preimage of complement"

Introduction "
In this level, we prove that $f^{-1}(A^c) = f^{-1}(A)^c$,
where $A^c$ is the complement of $A$ in the universe of discourse.
In Lean, this is denoted `Aᶜ` or `Set.compl A`, and can be written \\^c.
Recall that `x ∈ Aᶜ ↔ x ∉ A`.
"

open Set

--namespace function

/--
The theorem $f^{-1}(A^c) = f^{-1}(A)^c$
-/
TheoremDoc PreimageComplement as "PreimageComplement" in "function"

/-- Show that $f^{-1}(A^c) = f^{-1}(A)^c$. -/
Statement PreimageComplement {X Y : Type} (A : Set Y) (f : X → Y) : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ := by
  Hint "In this level, it can be useful to use `rw [mem_compl_iff]` or `rw [mem_compl_iff] at h` to rewrite at statement `a ∈ Sᶜ` to `a ∉ S`."
  Hint "Another useful technique is to use `by_contra` to do a proof by contradiction."
  ext y
  apply Iff.intro
  intro h
  rewrite [mem_compl_iff]
  by_contra h2
  exact h h2

  intro h
  rewrite [mem_compl_iff] at h
  rewrite [mem_preimage]
  rewrite [mem_compl_iff]
  by_contra h2
  exact h h2

Conclusion "
Level completed!
"
