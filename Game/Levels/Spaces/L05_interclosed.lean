import Game.Levels.Spaces.L04_complunion

open TopologicalSpace

namespace TTG

World "Spaces"
Level 5
Title "Family Intersection of Closed Sets"

Introduction "

"

/-- The intersection of a family of closed sets is closed. -/
TheoremDoc TTG.isClosed_sInter as "isClosed_sInter" in "topology"

/-  -/
Statement isClosed_sInter {U : Type} [h : TopologicalSpace U] {F : Set (Set U)} :
    (∀ A ∈ F, IsClosed A) → IsClosed (⋂₀ F) := by
  intro Acl
  rw [←isOpen_compl_iff]
  rw [compl_sInter]
  apply isOpen_sUnion
  intro B hB
  obtain ⟨A, AinF, rfl⟩ := hB
  rw [isOpen_compl_iff]
  exact Acl A AinF
