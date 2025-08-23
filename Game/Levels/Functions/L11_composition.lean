import Game.Levels.Functions.L10_preimage_image

World "Functions"
Level 11
Title "Composition of functions"

Introduction "
In this level, we introduce the composition of functions.
The composition of two functions $f : X \to Y$ and $g : Y \to Z$ is a function $g \\circ f : X \\to Z$ defined by $(g \\circ f)(x) = g(f(x))$ for all $x \\in X$.

In Lean, the composition of functions is denoted by `g ∘ f` or `Function.comp g f`.
To write the `∘` symbol, you can type `\\circ` in the editor.

In this level, we also introduce a new tactic, `use`, which is useful when working with images of functions.
If your goal is `y ∈ f '' A`, `use x` will change the goal to `x ∈ A` and `f x = y`.
"

open Set

/-- The theorem $(g \circ f)(A) = g(f(A))$. -/
TheoremDoc ImageComposition as "ImageComposition" in "function"

/-- Show that $(g \circ f)(A) = g(f(A))$. -/
Statement ImageComposition {X Y : Type} (A : Set X) (f : X → Y) (g : Y → Z) : (g ∘ f) '' (A) = g '' (f '' A)  := by
  Hint "The theorem `Function.comp_apply` can be used to rewrite `(g ∘ f) x` as `g (f x)`."
  ext y
  apply Iff.intro

  intro h
  obtain ⟨x, hx, rfl⟩ := h
  Hint "Try 'rewrite [Function.comp_apply]'."
  rewrite [Function.comp_apply]
  Hint "Now, you can use `use` to finish the subgoal. Try `use {f} {x}`."
  use f x
  apply And.intro
  use x
  rfl

  intro h
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨x, hx, rfl⟩ := hy
  Hint "Now, you can use `use` to finish the subgoal. Try `use {x}`."
  use x
  apply And.intro
  exact hx
  rfl


Conclusion "
Level completed!
"

/--
If your goal is `y ∈ f '' A`, `use x` will change the goal to `x ∈ A` and `f x = y`.
-/
TacticDoc use
NewTactic use

/--
The composition of two functions $f : X \to Y$ and $g : Y \to Z$ is a function $g \\circ f : X \\to Z$ defined by $(g \\circ f)(x) = g(f(x))$ for all $x \\in X$.

The theorem `Function.comp_apply` can be used to rewrite `(g ∘ f) x` as `g (f x)`.
-/
DefinitionDoc Function.comp as "g ∘ f"
NewDefinition Function.comp

/-- $(g \\circ f) (x) = g(f(x))$ -/
TheoremDoc Function.comp_apply as "Function.comp_apply" in "function"
NewTheorem Function.comp_apply
