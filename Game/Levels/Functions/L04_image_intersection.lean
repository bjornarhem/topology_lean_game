import Game.Levels.Functions.L03_image_union

World "Functions"
Level 4
Title "Image of intersection"

Introduction "

"

open Set

/-- The theorem $f(A ∩ B) ⊆ f(A) ∩ f(B)$. -/
TheoremDoc ImageIntersection as "ImageIntersection" in "function"

/-- Show that $f(A ∩ B) ⊆ f(A) ∩ f(B)$. -/
Statement ImageIntersection {X Y : Type} (A B : Set X) (f : X → Y) : f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) := by
  Hint "This level can be solved in a similar way to the previous one. You can start by introducing an element with `intro y`."
  intro y
  Hint "Now, `intro h` will introduce a hypothesis `h : {y} ∈ {f} '' ({A} ∩ {B})` and change you goal to `{y} ∈ {f}'' {A} ∩ {y} ∈ {f}'' {B}`."
  intro h
  Hint "Recall that for two sets `A` and `B`, `a ∈ A ∩ B` is equivalent to `a ∈ A ∧ a ∈ B`. Some useful techniques: `apply And.intro` will split the goal into two subgoals. For a hypothesis `h : a ∈ S ∩ T`, `h.left` gives you a proof of `a ∈ S` and `h.right` gives you a proof of `a ∈ T`."
  obtain ⟨x, hxAB, rfl⟩ := h
  apply And.intro
  exact ⟨x, hxAB.left, rfl⟩
  exact ⟨x, hxAB.right, rfl⟩

Conclusion "
Level completed!
"
