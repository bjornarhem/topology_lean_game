import Game.Levels.Spaces.L07_pairclosed

open Set
namespace TTG

World "Spaces"
Level 8
Title "Openness as a Local Property"

Introduction"

"

/-- -/
TheoremDoc TTG.isOpen_iff_forall_mem_open as "isOpen_iff_forall_mem_open" in "topology"

Statement isOpen_iff_forall_mem_open {X : Type} [h : TopologicalSpace X] (U : Set X) :
    IsOpen U ↔ ∀ x ∈ U, ∃ V ⊆ U, IsOpen V ∧ x ∈ V := by
  constructor
  · intro hU x xinU
    use U
  · intro prop
    have : U = ⋃₀ {V | V ⊆ U ∧ IsOpen V} := by
      ext x
      constructor
      · intro xinU
        rw [mem_sUnion]
        obtain ⟨V, VssU, hV, xinV⟩ := prop x xinU
        use V
        constructor
        · rw [mem_setOf]
          exact ⟨VssU, hV⟩
        · exact xinV
      · intro xinU₀
        rw [mem_sUnion] at xinU₀
        obtain ⟨V, hV, xinV⟩ := xinU₀
        rw [mem_setOf] at hV
        exact hV.left xinV
    rw [this]
    apply isOpen_sUnion
    intro V hV
    rw [mem_setOf] at hV
    exact hV.right
