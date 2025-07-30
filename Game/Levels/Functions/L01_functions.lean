import Game.Metadata

World "Functions"
Level 1
Title "Intro to functions"

Introduction "
Let's warm up with the following simple exercise.
"
/- TODO: write that we assume familiarity with the keywords from the set theory game. -/

/-- Show that if $x = y$, then $f(x) = f(y)$. -/
Statement {X Y : Type} (f : X → Y) (x y : X) (h : x = y) : f x = f y := by
  Hint "You can use the `subst` tactic to replace `y` with `x`. Typing either `subst h` or `subst y` will work."
  subst h
  Hint "Now you can use `rfl` to finish the proof. Recall that `rfl` means that the left-hand side and right-hand side of the equation are definitionally equal."
  rfl

Conclusion "
Level 1
"

NewTactic subst rfl intro exact obtain use apply cases left right ext «have»
NewTheorem Iff.intro Or.inl Or.inr
