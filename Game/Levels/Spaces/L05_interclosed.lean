import Game.Levels.Spaces.L04_complunion

open Set

namespace TTG

World "Spaces"
Level 5
Title "Family Intersection of Closed Sets"

Introduction "
In this level we ask you to prove that a family intersection of closed sets is closed.
"

/-- The intersection of a family of closed sets is closed. -/
TheoremDoc TTG.isClosed_sInter as "isClosed_sInter" in "topology"

/-  -/
Statement isClosed_sInter {U : Type} [TopologicalSpace U] {F : Set (Set U)} :
    (∀ A ∈ F, IsClosed A) → IsClosed (⋂₀ F) := by
  intro Acl
  rw [←isOpen_compl_iff]
  rw [compl_sInter]
  apply isOpen_sUnion
  intro B hB
  rw [mem_setOf] at hB
  rw [←compl_compl B, isOpen_compl_iff]
  exact Acl Bᶜ hB

Conclusion "Level Completed!"
