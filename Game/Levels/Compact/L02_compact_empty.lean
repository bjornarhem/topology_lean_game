import Game.Levels.Compact.L01_finite

open Set
namespace TTG

World "Compact"
Level 2
Title "Compact sets"

Introduction "
Now we can define compact sets.
A *cover* of a set `s` is a family of sets whose union contains `s`.  A set is *compact* if
every open cover of it has a finite subcover.  In Lean:
```
def IsCompact {X : Type} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ F : Set (Set X), (∀ U ∈ F, IsOpen U) → s ⊆ ⋃₀ F →
    ∃ G ⊆ F, G.Finite ∧ s ⊆ ⋃₀ G
```
In words: for every family `F` of open sets with `s ⊆ ⋃₀ F`, there is a subfamily
`G ⊆ F` which is finite and still satisfies `s ⊆ ⋃₀ G`.
Recall that you can enter the symbol `⋃₀` by typing `\\U0`, and `∅` by typing `\\empty`.

As with `IsConnected`, you can treat `IsCompact` as a theorem: typing `rw [IsCompact]` will
unfold the definition.  You don't have to, though — since the definition begins with a `∀`,
you can go straight in with `intro`.

To warm up, let's show that the empty set is compact.
"

def IsCompact {X : Type} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ F : Set (Set X), (∀ U ∈ F, IsOpen U) → s ⊆ ⋃₀ F →
    ∃ G ⊆ F, G.Finite ∧ s ⊆ ⋃₀ G

TheoremTab "Compact"

/-- The empty set is compact. -/
TheoremDoc TTG.empty_compact as "empty_compact" in "Compact"

/-- Show that the empty set is compact. -/
Statement empty_compact {X : Type} [TopologicalSpace X] : IsCompact (∅ : Set X) := by
  Hint "The definition starts with a `∀`, so begin by introducing the family and the two
  hypotheses about it: `intro F hopen hcover`."
  intro F hopen hcover
  Hint "You must produce a finite subfamily of `{F}` that still covers `∅`.  Since `∅` has
  no elements, how much of `{F}` do you actually need?"
  Hint (hidden := true) "Nothing at all — the empty family covers `∅`.  Try `use ∅`."
  use ∅
  Hint "Three things are left: that `∅ ⊆ {F}`, that `∅` is finite, and that `∅ ⊆ ⋃₀ ∅`."
  Hint (hidden := true) "Split them apart with `constructor`."
  constructor
  Hint (hidden := true) "`empty_subset {F}` proves this, from Empty World."
  exact empty_subset F
  constructor
  Hint (hidden := true) "This is `finite_empty`, which you were given in the last level."
  exact finite_empty
  Hint (hidden := true) "`empty_subset` again: `empty_subset (⋃₀ ∅)`."
  exact empty_subset (⋃₀ ∅)

Conclusion "
Well done!
"

/--
A set `s` is *compact* if every cover of `s` by open sets has a finite subcover:

```
def IsCompact {X : Type} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ F : Set (Set X), (∀ U ∈ F, IsOpen U) → s ⊆ ⋃₀ F →
    ∃ G ⊆ F, G.Finite ∧ s ⊆ ⋃₀ G
```

You can treat `IsCompact` as a theorem: `rw [IsCompact]` unfolds the definition.

To enter the symbol `⋃₀`, type `\U0`.
-/
DefinitionDoc IsCompact as "IsCompact"
NewDefinition IsCompact
