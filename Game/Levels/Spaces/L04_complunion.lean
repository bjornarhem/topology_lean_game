import Game.Levels.Spaces.L03_complinter

open Set

namespace TTG

World "Spaces"
Level 4
Title "Complement of Union"

Introduction "
Prove the symmetric result of the previous exercise.
"

/-- For any family of sets $F$, we have $(⋃_{A ∈ F} A) ^c = ⋂ _{A ∈ F} A^c$. -/
Statement {U : Type} (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {B | ∃ A ∈ F, B = Aᶜ} := by
  ext x
  constructor
  · intro h; rw [mem_compl_iff, mem_sUnion] at h; push_neg at h
    rw [mem_sInter]
    rintro _ ⟨A, AinF, rfl⟩
    rw [mem_compl_iff]
    exact h A AinF
  · intro h; rw [mem_sInter] at h
    rw [mem_compl_iff, mem_sUnion]; push_neg
    intro A AinF
    rw [←mem_compl_iff]
    apply h
    exact ⟨A, AinF, rfl⟩

Conclusion"
Level completed!
"
