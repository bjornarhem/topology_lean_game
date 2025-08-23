import Game.Levels.Functions.L01_functions

World "Functions"
Level 2
Title "Images of functions"

Introduction "
If $f \\colon X \\to Y$ and $A \\in X$, then the image of $A$ under $f$ is the set
$f(A) = \\{ f(x) \\mid x \\in A \\}$. In Lean, this is denoted `f '' A` or `image f A`.

A hypothesis `y ∈ f '' A ` decomposes as a triple `⟨x, hxA, rfl⟩`, where `x` is an element of `A`, `hxA` is the proof that `x ∈ A`, and `rfl` is the proof that `f x = y`. This is a common pattern when working with images in Lean.
In this level, we will use the `obtain` tactic to decompose such hypotheses.
Whenever you have a hypothesis of the form `h : y ∈ f '' A`, you can write `obtain ⟨x, hxA, rfl⟩ := h` to decompose it into its components.
To write the symbols `⟨` and `⟩`, you can write \\langle and \\rangle, respectively.

In this level, we prove the following property of images: If $A ⊆ B$, then $f(A) ⊆ f(B)$.
"

open Set

/--
If A ⊆ B, then $f(A) ⊆ f(B)$.
-/
TheoremDoc ImageSubset as "ImageSubset" in "function"

/-- If A ⊆ B, then $f(A) ⊆ f(B)$. -/
Statement ImageSubset {X Y : Type} (A B : Set X) (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  Hint "Let's star by choosing an element `y` in the left-hand side, using `intro`."
  intro y
  Hint "As usual when proving an implication, we can begin with `intro H`."
  intro H
  Hint "Use `obtain` to decompose the hypothesis `{y} ∈ f '' A` into a triple ⟨x, hxA, rfl⟩."
  obtain ⟨x, hxA, rfl⟩ := H
  Hint "You can use the keyword `have` to create the hypothesis `{x} ∈ B`."
  have hxB : x ∈ B := h hxA
  Hint "You can now complete the proof using `exact ⟨ {x}, {hxB}, rfl ⟩`."
  exact ⟨x, hxB, rfl⟩


Conclusion "
Well done!
If you don't want to use `obtain`, you can also apply the theorem `Set.mem_image`.
The command `rw [Set.mem_image] at h` will rewrite a hypothesis `h : y ∈ f '' A` into `∃ x ∈ A, f x = y`.
"

/--
If you have a hypothesis `y ∈ f '' A `, obtain ⟨x, hxA, rfl⟩ := h`
will introduce a new object `x`, a proof `hxA` that `x ∈ A`, and will rewrite `y` into `f x`.

To write the symbols `⟨` and `⟩`, you can write \\langle and \\rangle or \\< and \\>.
-/
TacticDoc obtain
NewTactic obtain

/-- $y$ is in $f(A)$ if and only if there exists a $x \in A$ such that $f(x) = y$. -/
TheoremDoc Set.mem_image as "Set.mem_image" in "function"

NewTheorem Set.mem_image

/-- Image of a set under a function. Can be written as `f '' A` or `Set.image f A`. -/
DefinitionDoc Set.image as "f '' A"
NewDefinition Set.image
