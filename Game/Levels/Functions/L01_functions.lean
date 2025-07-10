import Game.Metadata

World "Functions"
Level 1
Title "Intro to functions"

Introduction "
A message shown at the beginning of the level. Use it to explain any new concepts.
"

/-- Show that if $x = y$, then $f(x) = f(y)$. -/
Statement {X Y : Type} (f : X → Y) (x y : X) (h : x = y) : f x = f y := by
  Hint "You can use the `subst` tactic to replace `x` with `y`."
  subst h
  Hint "Now you can use `rfl` to finish the proof. Recall that `rfl` means that the left-hand side and right-hand side of the equation are definitionally equal."
  rfl

Conclusion "
The message shown when the level is completed
"

NewTactic subst rfl
