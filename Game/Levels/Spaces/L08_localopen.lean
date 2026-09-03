import Game.Levels.Spaces.L07_pairclosed

open Set
namespace TTG

World "Spaces"
Level 8
Title "Openness as a Local Property"

Introduction"
  In this level you will prove an important characterization of what it means to be an open set.
It could also be interpreted as the statement: Every topology is a basis generating itself.
"

/--Characterization of openness as a local property:

$U$ is open iff every point $x ∈ U$ admits an open neighbourhood $V$ contained in $U$.

In other words, every topology is a basis which generates itself.
 -/
TheoremDoc TTG.isOpen_iff_forall_mem_open as "isOpen_iff_forall_mem_open" in "topology"

/--$U$ is open iff every point $x ∈ U$ admits an open neighbourhood $V$ contained in $U$.-/
Statement isOpen_iff_forall_mem_open {X : Type} [TopologicalSpace X] (U : Set X) :
    IsOpen U ↔ ∀ x ∈ U, ∃ V ⊆ U, IsOpen V ∧ x ∈ V := by
  constructor
  · Hint (hidden := true) "This implication is quite direct.
    {U} is indeed an open neighbourhood of any point.

    The tactic `use` will automatically recognize the desired properties of {U}
    in the assumption list and close the goal, while `exact ⟨...⟩` will ask for
    precise proofs of each property."
    intro hU x xinU
    use U
  · intro pr
    Hint "It might be useful to prove the statement `U = ⋃₀ \{V | V ⊆ U ∧ IsOpen V}` before carrying on."
    have : U = ⋃₀ {V | V ⊆ U ∧ IsOpen V} := by
      ext x
      constructor
      · intro xinU
        rw [mem_sUnion]
        Hint (hidden := true) "`{pr} {x} {xinU}` has type `∃ V ⊆ U, IsOpen V ∧ x ∈ V`. Decompose it with `obtain`."
        obtain ⟨V, VssU, hV, xinV⟩ := pr x xinU
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
    Hint (hidden := true) "Use `rw[{this}]` on the goal, then apply `isOpen_sUnion`."
    rw [this]
    apply isOpen_sUnion
    intro V hV
    Hint (hidden := true) "Use `mem_setOf` to simplify the goal."
    rw [mem_setOf] at hV
    exact hV.right

Conclusion "
World completed! Now you have a solid grasp on working with open and closed sets!
"
