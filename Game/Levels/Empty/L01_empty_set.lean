import Game.Levels.Spaces.L02_closed
import Game.Levels.FamUnion.L06unionsub

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Empty"
Level 1
Title "The empty set"

Introduction "
In this level, we introduce the empty set, denoted `∅`.
We show that for any set $X$, the empty set is a subset of $X$.

The only thing you need to know about the empty set is that it has no elements.
This is stated in the theorem `Set.not_mem_empty`.
For any `x`, `Set.not_mem_empty x` is a proof that `x ∉ ∅`.
"

TheoremTab "∅"

/-- For any set $U$, we have that $∅ ⊆ U$. For any set `U`, `EmptySubset U` is a proof that `∅ ⊆ U`. -/
TheoremDoc EmptySubset as "EmptySubset" in "∅"

/-- For any set $U$, we have that $∅ ⊆ U$. -/
Statement EmptySubset {X : Type} (U : Set X) : ∅ ⊆ U := by
  Hint (hidden := true) "Start as you normally do when proving a subset relation, by introducing an arbitrary element `x` of the left-hand side and a hypothesis `h` that `x` is in the left-hand side."
  intro x
  intro h
  Hint "Recall that `Set.not_mem_empty {x}` is a proof that `x ∉ ∅`."
  Hint (hidden := true) "The tactic `by_contra` can be used here."
  by_contra
  have not_h := Set.not_mem_empty x
  exact not_h h

/-- No element is a member of the emptyset. For any `x`, `Set.not_mem_empty x` is a proof that `x ∉ ∅`. -/
TheoremDoc Set.not_mem_empty as "Set.not_mem_empty" in "∅"
NewTheorem Set.not_mem_empty


/--
The empty set, denoted `∅`, is the unique set with no elements.
To input the symbol `∅`, you can type `\empty`.

The theorem `Set.not_mem_empty` states that for any `x`, `Set.not_mem_empty x` is a proof that `x ∉ ∅`.
-/
DefinitionDoc Emptyset as "∅"
NewDefinition Emptyset
