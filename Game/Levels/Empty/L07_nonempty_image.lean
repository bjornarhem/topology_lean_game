import Game.Levels.Empty.L06_empty_image

open Set
namespace TTG

World "Empty"
Level 7
Title "Image of a nonempty empty set"

Introduction "
In this level, we show that the image of a nonempty set under any function is nonempty.
"

/-- If $f : X → Y$ is any function, and $U ⊆ X$ is nonempty, then $f(U)$ is nonempty. -/
TheoremDoc TTG.nonempty_image as "nonempty_image" in "∅"

/-- If $f : X → Y$ is any function, and $U ⊆ X$ is nonempty, then $f(U)$ is nonempty. -/
Statement nonempty_image {X Y : Type} (f : X → Y) (A : Set X) : A.Nonempty → (f '' (A)).Nonempty := by
  intro h
  Hint (hidden:=true) "Remember that `A.Nonempty` is defined as `∃ x, x ∈ A`. Thus, if you have a hypothesis `{h} : A.Nonempty`, you can use `obtain ⟨x, h1⟩ := {h}` to get an element `x` of `A`."
  obtain ⟨x, h1⟩ := h
  Hint (hidden:=true) "Here, you can use `rewrite [Set.nonempty_def]` to rewrite the goal into a form that is easier to prove. Often, rewriting in situations like this is optional, as Lean recognizes when expressions are definitionally equal. However, rewriting can make it easier for you to see how to proceed with the proof."
  rewrite [Set.nonempty_def]
  Hint (hidden:=true) "How do you finish a proof when the goal begins with `∃`?"
  use f x
  exact ⟨x, h1, rfl⟩
