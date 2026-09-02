import Game.Levels.Spaces.L02_closed

open Set

namespace TTG

World "Spaces"
Level 3
Title "Complement of Intersection"

Introduction "
In the two following levels, we take a break from topology and prove two set theoretic results
that are vital for adapting propositions about open sets to propositions
about closed sets and viceversa.
"

/-- For any family of sets $F$, we have $(⋂_{A ∈ F} A) ^c = ⋃ _{A ∈ F} A^c$. -/
TheoremDoc TTG.compl_sInter as "compl_sInter" in "⋂₀⋃₀"

/-- For any family of sets $F$, we have $(⋂_{A ∈ F} A) ^c = ⋃ _{A ∈ F} A^c$. -/
Statement compl_sInter {U : Type} (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {B | ∃ A ∈ F, B = Aᶜ} := by
  ext x
  constructor
  · intro h
    rw [mem_compl_iff] at h; rw [mem_sInter] at h; push_neg at h
    obtain ⟨A₀, A₀inF, xninA₀⟩ := h
    rw [mem_sUnion]
    use A₀ᶜ
    constructor
    · exact ⟨A₀, A₀inF, rfl⟩
    · rwa [mem_compl_iff]
  · intro h
    rw [mem_sUnion] at h
    obtain ⟨B₀, hB₀, xinB₀⟩ := h
    obtain ⟨A₀, A₀inF, rfl⟩ := hB₀
    rw [mem_compl_iff] at xinB₀
    rw [mem_compl_iff, mem_sInter]; push_neg
    exact ⟨A₀, A₀inF, xinB₀⟩

Conclusion "
Level completed!
"
