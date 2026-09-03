import Game.Levels.FamCombo
import Game.Levels.Functions

open Set
namespace TTG

World "Spaces"
Level 1
Title "Introduction to topological spaces"

Introduction "
In this level, we introduce the `TopologicalSpace` typeclass.
The statement `TopologicalSpace X` means that `X` is a topological space.
The `TopologicalSpace` typeclass is defined as follows:
```
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```
It's okay if you don't understand all of this.
We will only focus on some of it now, and get to the rest in later worlds.

The first line says which sets are open.  For a set `U : Set X`, the statement `IsOpen U`
says that `U` is open.  Like `x ∈ U` or `A ⊆ B`, this is a *statement*: it is either true or
false, and it is something you prove.  You never have to say *which* topology you mean —
Lean works that out from the type of `U`.

The other three lines are the axioms of a topological space, and you can use them as
theorems:
* `isOpen_univ` is a proof that the whole space is open.
* `isOpen_inter hU hV` is a proof of `IsOpen (U ∩ V)`, given `hU : IsOpen U` and
  `hV : IsOpen V`.
* `isOpen_sUnion` says that a union of a family of open sets is open.

Observe that It's not explicitly stated in the axioms that the empty set is open,
because this follows from the fact that a union of open sets is open, applied to the empty union.
We will prove this in a later level!

We start with a warm-up exercise.
"

/-- If `U` and `V` are open, then so is `U ∩ V`.  This is one of the axioms of a
topological space, restated so that you can use it without a prefix. -/
theorem isOpen_inter {X : Type} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) := hU.inter hV

/-- Show that if $U, V$ and $W$ are open sets in $X$, then $U ∩ V ∩ W$ is open. -/
Statement {X : Type} [TopologicalSpace X] (U V W : Set X) : (IsOpen U) → (IsOpen V) → (IsOpen W) → IsOpen (U ∩ V ∩ W) := by
  Hint "Start by introducing three hypotheses, with `intro hU hV hW`."
  intro hU hV hW
  Hint "Now you can use `isOpen_inter` to prove that the intersection of two open sets is open. For example, try `have hUV := isOpen_inter {hU} {hV}`."
  have hUV := isOpen_inter hU hV
  Hint "Finish by using `isOpen_inter` again. You might need to rewrite using `inter_assoc` and/or `inter_comm`."
  exact isOpen_inter hUV hW


Conclusion "
Good job!
In future levels, you can always look up the definition of `TopologicalSpace` in the right column.
Here you will also find the predicates and axioms belonging to the TopologicalSpace typeclass, such as `IsOpen` and `isOpen_univ`.
"

/--
The `TopologicalSpace` typeclass is defined as follows:

```
class TopologicalSpace (X : Type u) where
  protected IsOpen : Set X → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

The first line says which sets are open.  For a set `U : Set X`, the statement `IsOpen U`
says that `U` is open.  Like `x ∈ U` or `A ⊆ B`, this is a *statement*: it is either true or
false, and it is something you prove.  You never have to say *which* topology you mean —
Lean works that out from the type of `U`.

The other three lines are the axioms of a topological space, and you can use them as
theorems:

* `isOpen_univ` is a proof that the whole space is open.
* `isOpen_inter hU hV` is a proof of `IsOpen (U ∩ V)`, given `hU : IsOpen U` and
  `hV : IsOpen V`.
* `isOpen_sUnion` says that a union of a family of open sets is open.
-/
DefinitionDoc TopologicalSpace as "TopologicalSpace"

/--
For a set `U` in a topological space, `IsOpen U` is the statement that `U` is open.

It is a statement, not a number or a `Bool`: it is either true or false, and it is something
you prove.  You do not have to say which topology you mean; Lean infers that from the type
of `U`.
-/
DefinitionDoc IsOpen as "IsOpen"

NewDefinition TopologicalSpace IsOpen

/-- `isOpen_univ` is a proof that the whole space is open. -/
TheoremDoc isOpen_univ as "isOpen_univ" in "topology"

/-- Given `hU : IsOpen U` and `hV : IsOpen V`, `isOpen_inter hU hV` proves `IsOpen (U ∩ V)`. -/
TheoremDoc TTG.isOpen_inter as "isOpen_inter" in "topology"

/-- If every member of a family `F` is open, then `isOpen_sUnion` proves `IsOpen (⋃₀ F)`. -/
TheoremDoc isOpen_sUnion as "isOpen_sUnion" in "topology"

NewTheorem isOpen_univ TTG.isOpen_inter isOpen_sUnion
