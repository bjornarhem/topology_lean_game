import Game.Levels.Continuous.L02_is_continuous

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
namespace TTG

World "Empty"
Level 1
Title "The empty set"

Introduction "
In this level, we introduce the empty set, denoted `∅`.
We show that for any set $X$, the empty set is a subset of $X$.

The only thing you need to know about the empty set is that it has no elements.
This is stated in the theorem `Set.notMem_empty`.
For any `x`, `Set.notMem_empty x` is a proof that `x ∉ ∅`.
"

TheoremTab "∅"

/-- For any set $U$, we have that $∅ ⊆ U$. For any set `U`, `empty_subset U` is a proof that `∅ ⊆ U`. -/
TheoremDoc TTG.empty_subset as "empty_subset" in "∅"

/-- For any set $U$, we have that $∅ ⊆ U$. -/
Statement empty_subset {X : Type} (A : Set X) : ∅ ⊆ A := by
  Hint (hidden := true) "Start as you normally do when proving a subset relation, by introducing an arbitrary element `x` of the left-hand side and a hypothesis `h` that `x` is in the left-hand side."
  intro x
  intro h
  Hint "Recall that `Set.notMem_empty {x}` is a proof that `{x} ∉ ∅`."
  Hint (hidden := true) "The tactic `by_contra` can be used here."
  by_contra
  have not_h := Set.notMem_empty x
  exact not_h h

/-- No element is a member of the emptyset. For any `x`, `Set.notMem_empty x` is a proof that `x ∉ ∅`. -/
TheoremDoc Set.notMem_empty as "Set.notMem_empty" in "∅"
NewTheorem Set.notMem_empty


/--
The empty set, denoted `∅`, is the unique set with no elements.
To input the symbol `∅`, you can type `\empty`.

The theorem `Set.notMem_empty` states that for any `x`, `Set.notMem_empty x` is a proof that `x ∉ ∅`.
-/
DefinitionDoc Emptyset as "∅"
NewDefinition Emptyset
