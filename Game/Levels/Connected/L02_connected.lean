import Game.Levels.Connected.L01_preconnected

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Connected"
Level 2
Title "Connected sets"

Introduction "
In this level, we introduce connected sets.

The `Connected` property is simple. It's defined as follows.
```
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```
In words, a set `s` in a topological space `α` is _connected_ if it is nonempty and preconnected.

As for `IsPreconnected`, you can treat `IsConnected` as a theorem. Typing `rw [IsConnected]` will unfold the definition.

As a warm-up, we show that the empty set is not connected.
"

/-- The empty set is not connected. -/
Statement {X : Type} [h : TopologicalSpace X] : ¬ IsConnected (∅ : Set X) := by
  rw [IsConnected]
  push_neg
  intro h
  by_contra
  rw [NonemptyIffNotEmpty] at h
  exact h rfl


/--
The `Connected` property is defined as follows.
```
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```
In words, a set `s` in a topological space `α` is _connected_ if it is nonempty and preconnected.

You can treat `IsConnected` as a theorem. Typing `rw [IsConnected]` will unfold the definition.
-/
DefinitionDoc Connected as "Connected"
NewDefinition Connected
