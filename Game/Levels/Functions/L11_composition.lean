import Game.Levels.Functions.L10_preimage_image

World "Functions"
Level 11
Title "Composition of functions"

Introduction "
In this level, we introduce the composition of functions.
The composition of two functions $f : X \to Y$ and $g : Y \to Z$ is a function $g \\circ f : X \\to Z$ defined by $(g \\circ f)(x) = g(f(x))$ for all $x \\in X$.

In Lean, the composition of functions is denoted by `g ∘ f` or `Function.comp g f`.
To write the `∘` symbol, you can type `\\circ` in the editor.
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
  rewrite [Function.comp_apply]
  use f x
  apply And.intro
  use x
  rfl

  intro h
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨x, hx, rfl⟩ := hy
  use x
  apply And.intro
  exact hx
  rfl


Conclusion "
Level completed!
"

/-- TODO: Docstring for g ∘ f -/
DefinitionDoc Function.comp as "g ∘ f"
NewDefinition Function.comp

/-- $(g \\circ f) (x) = g(f(x))$ -/
TheoremDoc Function.comp_apply as "Function.comp_apply" in "function"
NewTheorem Function.comp_apply
