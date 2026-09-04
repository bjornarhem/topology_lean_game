import Game.Levels.Connected.L02_connected

open Set
namespace TTG

World "Connected"
Level 3
Title "Singletons are connected"

Introduction "
In this level, we show that a one-element set is connected.
"

/-- Show that a one-element set is connected. -/
Statement {X : Type} [TopologicalSpace X] (x : X) :
    IsConnected ({x} : Set X) := by
  Hint "Unfold the definition with `rw [IsConnected]`, then split the two halves with `constructor` or `apply And.intro`."
  rw [IsConnected]
  constructor
  Hint (hidden := true) "`use {x}`, and then `rfl` finishes it."
  use x
  rfl
  Hint "It remains to show preconnectedness. Introduce the two open sets and all the hypotheses about them."
  Hint (hidden := true) "`intro u v hu hv hcover hxu hxv`"
  intro u v hu hv hcover hxu hxv

  Hint "Which element can you `use` to show that `\{{x}} ∩ ({u} ∩ {v})` is nonempty?"
  Hint (hidden := true) (strict:=true) "`use {x}`"
  use x
  Hint (hidden:=true) "Writing `obtain ⟨a, haX, hau⟩ := {hxu}` gives you an element `a` contained in both `{u}` and `\{{x}}`."
  constructor
  rfl
  constructor

  obtain ⟨a, haX, hau⟩ := hxu
  Hint (hidden:=true) "`{haX}` says that `{a}` is a member of `\{{x}}`. Which theorem turns that into an equation?"
  rw [mem_singleton_iff] at haX
  rw [← haX]
  exact hau

  obtain ⟨b, hbX, hbu⟩ := hxv
  rw [mem_singleton_iff] at hbX
  rw [← hbX]
  exact hbu

Conclusion "
Goal defeated! The singleton space never stood a chance.
"
