import Game.Levels.Empty

open Set
namespace TTG

World "Hausdorff"
Level 1
Title "Closed Singletons"

Introduction "
In this level, we introduce the `T2Space` typeclass.
The proposition `T2Space X` means that the topological space X is a Hausdorff space.

We define the `T2Space` typeclass in the following manner:

```
T2Space (X : Type u) [TopologicalSpace X] : Prop where
  t2 : ∀ x y : X, x ≠ y → ∃ (u : Set X) (v : Set Y), isOpen u ∧ isOpen v ∧ x ∈ u ∧ x ∈ v ∧ u ∩ v = ∅
```

An important thing to notice is that `T2Space` does not rehash the properties of a general topological space.
Also, the predicate `[TopologicalSpace X]` appears in its sequence of arguments.
Thus, we can only say `X` is a `T2Space` when we already know it is a `TopologicalSpace`.

Note also that we call Hausdorff spaces `T2Spaces`.
This is a mathematical convention that exists outside of Lean to describe several separation axioms:

T_1 space: a space where all singletons are closed
T_2 space (Hausdorff): a space where two distinct points can be separated
T_3 space (regular): a T_1 space where a point and a closed set can be separated
T_4 space (normal): a T_1 space where two closed sets can be separated

Why do you think they are arranged in this particular order?

As a hint to the question above, in this exercise we will prove that all T_2 spaces are also T_1 spaces.
"

/--
We define the `T2Space` typeclass in the following manner:

```
T2Space (X : Type u) [TopologicalSpace X] : Prop where
  t2 : ∀ x y : X, x ≠ y → ∃ (u : Set X) (v : Set Y), isOpen u ∧ isOpen v ∧ x ∈ u ∧ x ∈ v ∧ u ∩ v = ∅
```
-/
DefinitionDoc T2Space as "T2Space"
NewDefinition T2Space

class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  t2 : ∀ x y : X, x ≠ y → ∃ (u : Set X) (v : Set X), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

Statement {X : Type} [TopologicalSpace X] [T2 : T2Space X] (U V : Set X) : ∀ x : X, IsClosed {x} := by
  intro x
  rw [←isOpen_compl_iff]
  Hint "You can use `isOpen_iff_forall_mem_open`."
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  Hint (hidden := true) "Rewrite {hy} into a more suitable form."
  rw [mem_compl_iff, Set.mem_singleton_iff] at hy
  Hint "Now you can use the fact that the space is Hausdorff."
  Hint (hidden := true) "Add the assumption `{T2}.t2 {y} {x} {hy}`."
  have sep := T2.t2 y x hy
  obtain ⟨U, V, hU, hV, yinU, xinV, UVdisj⟩ := sep
  Hint "Pair the `use` tactic with a suitable object that is already in your assumption list."
  Hint (hidden := true) "{U} should do the trick."
  use U
  constructor
  · intro z zinU
    Hint (hidden := true) "Use `by_contra`."
    by_contra abs
    rw [mem_compl_iff] at abs
    push_neg at abs
    rw [Set.mem_singleton_iff] at abs
    Hint (hidden := true) "Combining {abs}, {zinU} and {xinV} should yield
    a statement in contradiction with {UVdisj}."
    rw [abs] at zinU
    have UVndisj : Set.Nonempty (U ∩ V) := by
      rw [Set.nonempty_def]
      exact ⟨x, zinU, xinV⟩
    rw [nonempty_iff_not_empty] at UVndisj
    exact UVndisj UVdisj
  · exact ⟨hU, yinU⟩

Conclusion"
Level finished! Well done!
"
