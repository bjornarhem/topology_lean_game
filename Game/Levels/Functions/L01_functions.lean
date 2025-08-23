import Game.Levels.Comp

World "Functions"
Level 1
Title "Intro to functions"

Introduction "
Let's warm up with the following simple exercise.
"

/-- Show that if $x = y$, then $f(x) = f(y)$. -/
Statement {X Y : Type} (f : X → Y) (x y : X) (h : x = y) : f x = f y := by
  Hint "You can use the `rewrite [h]` to replace `x` with `y`."
  rewrite [h]
  Hint "Now you can use `rfl` to finish the proof. Recall that `rfl` means that the left-hand side and right-hand side of the equation are definitionally equal."
  rfl

Conclusion "
Level 1
"

--NewTactic subst rfl intro exact obtain use apply cases left right ext «have» by_contra push_neg rewrite
--
--TheoremDoc Iff.intro as "Iff.intro" in "Logic"
--TheoremDoc Or.inl as "Or.inl" in "Logic"
--TheoremDoc Or.inr as "Or.inr" in "Logic"
--TheoremDoc And.intro as "And.intro" in "Logic"
--NewTheorem Iff.intro Or.inl Or.inr And.intro Set.mem_inter_iff Set.mem_union Set.mem_compl_iff
--
--/-- Intersection of sets. To enter the symbol `∩`, type `\cap` of `\inter`. -/
--DefinitionDoc Set.inter as "∩"
--
--/-- Intersection of sets. To enter the symbol `∪` type `\cup` or `\union`. -/
--DefinitionDoc Set.union as "∪"
--
--/-- Complement of a set. To enter the symbol `ᶜ`, type `\^c` or `\compl`. -/
--DefinitionDoc Set.compl as "ᶜ"
--
--NewDefinition Set.inter Set.union Set.compl
