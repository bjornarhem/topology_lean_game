import Game.Levels.Combo

open Set (mem_inter_iff mem_union Subset.antisymm)
open TopologicalSpace
open STG4

World "Spaces"
Level 1
Title "Introduction to topological spaces"

Introduction "
In this level, we introduce the `TopologicalSpace` typeclass.
The statement `TopologicalSpace X` means that `X` is a topological space.

The `TopologicalSpace` typeclass is defined as follows:

```
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

It's okay if you don't understand all of this.
We will only focus on some of it now, and get to the rest in later worlds.

The `IsOpen` predicate is used to determine whether a set is open in the topological space.
You can treat it as a function: given `h : TopologicalSpace X` and `U : Set X`,
the expression `h.IsOpen U` returns `true` if `U` is open and `false` otherwise.

The other three lines are the axioms of a topological space.
You can treat them as theorems: If `U` and `V` are open set in `X`,
and you have hypotheses `hU : h.IsOpen U` and `hV : h.IsOpen V`,
then `h.isOpen_inter U V hU hV` is a proof of `h.IsOpen (U ∩ V)`.

Note also that it Lean, it often suffices to write `IsOpen U` instead of `h.IsOpen U`.
This is because Lean can often infer the topological space from the type of `U`.

Observe that It's not explcitly stated in the axioms that the empty set is open,
because this follows from the fact that a union of open sets is open, applied to the empty union.
We will prove this in a later level!

We start with a warm-up exercise.
"

/-- Show that if $U, V$ and $W$ are open sets in $X$, then $U ∩ V ∩ W$ is open. -/
Statement {X : Type} [h : TopologicalSpace X] (U V W : Set X) : (IsOpen U) → (IsOpen V) → (IsOpen W) → IsOpen (U ∩ V ∩ W) := by
  Hint "Start by introducing three hypotheses, with `intro hU hV hW`."
  intro hU hV hW
  Hint "Now, you can use `{h}.isOpen_inter` to prove that the intersection of two open sets is open. For example, try `have hUV := h.isOpen_inter {U} {V} {hU} {hV}`."
  have hUV := h.isOpen_inter U V hU hV
  Hint "Finish by using `{h}.isOpen_inter` again. You might need to rewrite using `inter_assoc` and/or `inter_comm`."
  have hUVW := h.isOpen_inter (U ∩ V) W hUV hW
  exact hUVW


Conclusion "
Level completed!
"

/--
The `TopologicalSpace` typeclass is defined as follows:

```
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

The `IsOpen` predicate is used to determine whether a set is open in the topological space.
You can treat it as a function: given `h : TopologicalSpace X` and `U : Set X`,
the expression `h.IsOpen U` returns `true` if `U` is open and `false` otherwise.

The other three lines are the axioms of a topological space.
You can treat them as theorems: If `U` and `V` are open set in `X`,
and you have hypotheses `hU : h.IsOpen U` and `hV : h.IsOpen V`,
then `h.isOpen_inter U V hU hV` is a proof of `h.IsOpen (U ∩ V)`.

Note also that it Lean, it often suffices to write `IsOpen U` instead of `h.IsOpen U`.
This is because Lean can often infer the topological space from the type of `U`.
-/
DefinitionDoc TopologicalSpace as "TopologicalSpace"
NewDefinition TopologicalSpace
