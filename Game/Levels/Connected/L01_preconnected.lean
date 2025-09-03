import Game.Levels.Empty.L08_empty_inter

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Connected"
Level 1
Title "Preconnected sets"

Introduction "
In this level, we introduce preconnected sets.

The `IsPreconnected` property is defined as follows.
```
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
```
In words, a set `s` in a topological space `α` is _preconnected_ if,
for any two open sets `u` and `v` in `α`  such that
`s ⊆ u ∪ v`, `s ∩ u` is nonempty and `s ∩ v` is nonempty,
we have that `s ∩ (u ∩ v)` is nonempty.

You can treat `IsPreconnected` as a theorem. Typing `rw [IsPreconnected]` will unfold the definition.
"

/-- The empty set is preconnected. -/
Statement {X : Type} [h : TopologicalSpace X] : IsPreconnected (∅ : Set X) := by
  Hint "You can begin unwrapping the `IsPreconnected` definition by introducing several variables and hypotheses, like so: `intro V W hV hW hVWunion hV1 hW1`."
  intro V W hV hW hUnion hV1 hW1
  Hint (hidden := true) "Use the theorem `EmptyInter` to show that `{V} ∩ ∅ = ∅`."
  Hint (hidden := true) "Remember that we proved the theorem `NonemptyIffNotEmpty` the Empty world, which says that a set is `Nonempty` if and only it is not equal to the empty set. You can use that to create a contradiction here."
  rw [EmptyInter] at hV1
  rw [NonemptyIffNotEmpty] at hV1
  Hint (hidden := true) "If you have `{hV1}: ¬ (∅ = ∅)`, then `{hV1} rfl` is a proof of `false`."
  by_contra
  exact hV1 rfl


/--
The `IsPreconnected` property is defined as follows.
```
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
```
In words, a set `s` in a topological space `α` is _preconnected_ if,
for any two open sets `u` and `v` in `α`  such that
`s ⊆ u ∪ v`, `s ∩ u` is nonempty and `s ∩ v` is nonempty,
we have that `s ∩ (u ∩ v)` is nonempty.

You can treat `IsPreconnected` as a theorem. Typing `rw [IsPreconnected]` will unfold the definition.
-/
DefinitionDoc IsPreconnected as "IsPreconnected"
NewDefinition IsPreconnected
