import Game.Metadata

World "Functions"
Level 2
Title "Images of functions"

Introduction "
If $f \\colon X \\to Y$ and $A \\in X$, then the image of $A$ under $f$ is the set
$f(A) = \\{ f(x) \\mid x \\in A \\}$. In lean, this is denoted `f '' A` or `image f A`.

A hypothesis `y ∈ f '' A ` decomposes as a triple ⟨x, hxA, rfl⟩, where `x` is an element of `A`, `hxA` is the proof that `x ∈ A`, and `rfl` is the proof that `f x = y`. This is a common pattern when working with images in Lean.
In this level, we will use the `rintro` tactic to decompose such hypotheses. The `rintro` tactic is a combination of `intro` and `rfl`, which allows us to introduce variables and patterns in one step.
Whenever you introduce a hypothesis of the form `y ∈ f '' A`, you can write `rintro ⟨x, hxA, rfl⟩` to immediately decompose it into its components.
To write the symbols `⟨` and `⟩`, you can write \\langle and \\rangle, respectively.

We start by proving a property of images: if $A ⊆ B$, then $f(A) ⊆ f(B)$.
"

open Set

/-- If A ⊆ B, then $f(A) ⊆ f(B)$. -/
Statement ImageSubset {X Y : Type} (A B : Set X) (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  /- TODO: let the user reference this theorem later -/
  Hint "Let's star by choosing an element `y` in the left-hand side, using `intro`."
  intro y
  Hint "Use `rintro` to introduce the hypothesis `y ∈ f '' A` and decompose it into a triple ⟨x, hxA, rfl⟩."
  rintro ⟨x, hxA, rfl⟩
  Hint "You can use the keyword `have` to create the hypothesis `x ∈ B`."
  have hxB : x ∈ B := h hxA
  Hint "You can now complete the proof using `exact ⟨ x, hxB, rfl ⟩`."
  exact ⟨x, hxB, rfl⟩


Conclusion "
Well done!
If you don't want to use `rintro`, you can also apply the theorem `Set.mem_image`.
The command `rw [Set.mem_image] at h` will rewrite a hypothesis `h : y ∈ f '' A` into `∃ x ∈ A, f x = y`.
"

NewDefinition Set.image
NewTactic rintro
NewTheorem Set.mem_image
