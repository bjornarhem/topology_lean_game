import Game.Metadata

World "Functions"
Level 5
Title "Preimages of functions"

Introduction "
In this level, we introduce preimages of functions.
The preimage of a set $A$ under a function $f$ is the set of all elements in the domain of $f$ that map to elements in $A$.
In Lean, this is denoted `f ⁻¹' A`, which can be typed as `\\-1` followed by `'`, or written as `Set.preimage f A`.

The theorem `Set.mem_preimage` states that an element $x$ is in the preimage of $A$ under $f$ if and only if $f(x)$ is in $A$.
You can use the command `rewrite [Set.mem_preimage]` to rewrite a hypothesis of the form `x ∈ f ⁻¹' A` into `f x ∈ A`.
"

open Set

namespace function

/-- If A ⊆ B, then $f^{-1}(A) ⊆ f^{-1}(B)$. -/
Statement PreimageSubset {X Y : Type} (A B : Set Y) (f : X → Y) (h : A ⊆ B) : f ⁻¹' A ⊆ f ⁻¹' B := by
  Hint "Let's start by choosing an element `x` in the left-hand side, using `intro`."
  intro x
  Hint "As usual when proving an implication, we can begin with `intro H`."
  intro H
  Hint "Try `rewrite [Set.mem_preimage] at {H}`, followed by `rewrite [Set.mem_preimage]`."
  rewrite [Set.mem_preimage] at H
  rewrite [Set.mem_preimage]
  Hint "Recall that `{h} : A ⊆ B` is a proof that `a ∈ A` implies `a ∈ B`. You can use this to finish the level."
  exact h H

Conclusion "
Level completed!
"

/-- $x$ is in $f^{-1}(A)$ if and only if $f(x) \in A$. -/
TheoremDoc Set.mem_preimage as "Set.mem_preimage" in "function"
NewTheorem Set.mem_preimage

/-- Preimage of a set under a function. To write the preimage, use `f ⁻¹' A`, which can be typed as `\-1` followed by `'`, or write  `Set.preimage f A`. -/
DefinitionDoc Set.preimage as "f ⁻¹' A"
NewDefinition Set.preimage
