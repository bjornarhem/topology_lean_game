import Game.Metadata

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

The `IsOpen` predicate is used to determine whether a set is open in the topological space.
You can treat it as a function: given `h : TopologicalSpace X` and `U : Set X`,
the expression `h.IsOpen U` returns `true` if `U` is open and `false` otherwise.

The other three lines are the axioms of a topological space.
You can treat them as theorems: If `U` and `V` are open set in `X`,
and you have hypotheses `hU : h.IsOpen U` and `hV : h.IsOpen V`,
then `h.isOpen_inter U V hU hV` is a proof of `h.IsOpen (U ∩ V)`.

Note that It's not explcitly stated in the axioms that the empty set is open,
because this follows from the fact that a union of open sets is open, applied to the empty union.
We will prove this in a later level!

We start with a warm-up exercise.
"

open TopologicalSpace Set
namespace topology

/-- Show that if $U, V$ and $W$ are open sets in $X$, then $U ∩ V ∩ W$ is open. -/
Statement {X : Type} [h : TopologicalSpace X] {U V W : Set X} : (h.IsOpen U) → (h.IsOpen V) → (h.IsOpen W) → h.IsOpen (U ∩ V ∩ W) := by
  Hint "Start by introducing three hypotheses, with `intro hU hV hW`."
  intro hU hV hW
  Hint "Now, you can use `{h}.isOpen_inter` to prove that the intersection of two open sets is open. For example, try `have hUV := h.isOpen_inter {U} {V} {hU} {hV}`."
  have hUV := h.isOpen_inter U V hU hV
  Hint "Finish by using `{h}.isOpen_inter` again. You might need to rewrite using `Set.inter_assoc` and/or `Set.inter_comm`."
  have hUVW := h.isOpen_inter (U ∩ V) W hUV hW
  exact hUVW

/- TODO: introduce the empty set at some point. -/
-- A final note. In the problem statement, we write `h.IsOpen ∅` instead of `IsOpen ∅`.
-- This is because Lean cannot automatically infer the type of `∅` if we write `IsOpen ∅`.
-- We could also have written `IsOpen (∅ : Set X)`.
-- In the statement, `h` is simply the hypothesis that `X` is a topological space.
-- /-- Show that in any topological space, the empty set is open. -/
-- Statement empty_set_is_open {X : Type} [h: TopologicalSpace X]: h.IsOpen ∅ := by
--   have H := h.isOpen_sUnion ∅
--   apply H


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
You can treat it as a function: `IsOpen U` returns `true` if `U` is open and `false` otherwise.

The other three lines are the axioms of a topological space.
You can treat them as theorems: If `U` and `V` are open set in `X`,
and you have hypotheses `hU : IsOpen U` and `hV : IsOpen V`,
then `isOpen_inter hU hV` is a proof of `IsOpen (U ∩ V)`.
-/
DefinitionDoc TopologicalSpace as "TopologicalSpace"
NewDefinition TopologicalSpace

NewTheorem Set.inter_assoc Set.inter_comm Set.union_assoc Set.union_comm
