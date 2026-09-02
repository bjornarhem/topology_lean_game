import Game.Levels.Functions.L06_preimage_union

open Set
namespace TTG

World "Functions"
Level 7
Title "Preimage of intersection"

Introduction "
Try to solve it using what you've learned so far! Hints are available if you get stuck.
"

/-- The theorem $f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B)$. -/
TheoremDoc TTG.preimage_intersection as "preimage_intersection" in "function"

/-- Show that $f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B)$. -/
Statement preimage_intersection {X Y : Type} (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = (f ⁻¹' A) ∩ (f ⁻¹' B) := by
  Hint (hidden:=true) "Do you remember how to prove that two sets are equal? You want to use the `ext` tactic, followed by splitting the `↔` statement into two subgoals."
  ext x
  apply Iff.intro

  Hint (hidden:=true) "Recall that a membership in an intersection is equivalent to an `∧` statement (via `mem_inter_iff`). Do you remember which theorems and tactics are relevant for proving an `∧` statement? You can always check the definitions tab to read about `∧` and other symbols."
  intro h
  apply And.intro
  exact h.left
  exact h.right

  intro h
  apply And.intro
  exact h.left
  exact h.right


Conclusion "
Level completed!
"

DisabledTactic constructor
