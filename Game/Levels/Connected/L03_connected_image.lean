import Game.Levels.Connected.L02_connected

open Set (mem_inter_iff mem_union Subset.antisymm mem_sUnion mem_sInter)
open TopologicalSpace
open STG4

World "Connected"
Level 3
Title "Continuous image of a connected set"

Introduction "
This level is the hardest one in this Game so far.
But, by now, you have all the necessary tools to complete it.

Some general tips for this level:
* Many of the theorems you have proved in previous worlds can be applied here to make the proof simpler.
* You can use the `have` tactic to prove a statement over multiple lines. Look up the documentation in the right column for more details.
* If you get stuck, try solving the problem with pen and paper first.

Good luck!
"

/-- The continuous image of a connected set is connected -/
Statement {X Y : Type} [hX : TopologicalSpace X] [hY : TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (A : Set X) : (IsConnected A) → IsConnected (f '' A) := by
  -- First part: Prove that f(A) is nonempty
  intro hA
  apply And.intro
  have Unonempty := hA.left
  exact NonemptyImage f A Unonempty

  -- Second part: Prove that f(A) is preconnected
  have Apreconnected := hA.right
  intro V W hV hW hUnion hV1 hW1

  have hV_preim_open := hf.isOpen_preimage V hV
  have hW_preim_open := hf.isOpen_preimage W hW

  -- f^{-1}(V) nonempty
  obtain ⟨y, hy, hyV⟩ := hV1
  obtain ⟨a, haA, rfl⟩ := hy
  have hA_V_preim_nonempty : Set.Nonempty (A ∩ f ⁻¹' V)
  use a
  apply And.intro
  exact haA
  exact hyV

  -- f^{-1}(W) nonempty
  obtain ⟨z, hz, hzW⟩ := hW1
  obtain ⟨b, hbA, rfl⟩ := hz
  have hA_W_preim_nonempty : Set.Nonempty (A ∩ f ⁻¹' W)
  use b
  apply And.intro
  exact hbA
  exact hzW

  -- A \subset f^{-1}(V) ∪ f^{-1}(W)
  have hA_VW_preim_union : A ⊆ (f ⁻¹' V) ∪ (f ⁻¹' W)
  rw [← PreimageUnion]
  have h_1 := PreimageSubset (f '' A) (V ∪ W) f hUnion
  have h_2 := PreimageImage A f
  exact Subset.trans h_2 h_1

  -- Using preconnectedness of A to conclude
  have hVW_preim_nonempty := Apreconnected (f ⁻¹' V) (f ⁻¹' W) hV_preim_open hW_preim_open hA_VW_preim_union hA_V_preim_nonempty hA_W_preim_nonempty
  obtain ⟨x, hxA, hxVW_preim⟩ := hVW_preim_nonempty
  use (f x)
  apply And.intro
  exact ⟨x, hxA, rfl⟩
  rw [← PreimageIntersection] at hxVW_preim
  exact hxVW_preim
