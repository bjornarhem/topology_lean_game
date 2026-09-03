import Game.Levels.Empty

open Set
namespace TTG

World "Compact"
Level 1
Title "Finite sets"

Introduction "
To talk about compact sets, we first need to talk about *finite* sets.

In Lean, the statement that a set `S` is finite is written `S.Finite` (or `Set.Finite S`).

The most useful fact about finite sets is that a subset of a finite set is again finite:
if `h : S.Finite` and `h2 : T ⊆ S`, then `Finite.subset h h2` is a proof that `T.Finite`.
You can also write this as `h.subset h2`.

In this level, use it to show that the intersection of a finite set with any set is finite.
"

TheoremTab "Finite"

/-- If $A$ is finite, then $A \cap B$ is finite. -/
TheoremDoc TTG.inter_finite as "inter_finite" in "Finite"

/-- Show that if $A$ is finite, then $A \cap B$ is finite. -/
Statement inter_finite {X : Type} (A B : Set X) (hA : A.Finite) : (A ∩ B).Finite := by
  Hint "`Finite.subset` needs two things: a set you already know is finite, and a proof
  that your set is a subset of it.  You have `{hA}` already, so what is left to prove?"
  Hint (hidden := true) "Use `have` to prove `A ∩ B ⊆ A` first.  You proved exactly this
  statement back in Intersection World."
  have h : A ∩ B ⊆ A := by
    intro x hx
    exact hx.left
  Hint "Now combine `{hA}` and `{h}`."
  Hint (hidden := true) "`Finite.subset {hA} {h}` is a proof of the goal.  You could
  also write it as `{hA}.subset {h}`."
  exact Finite.subset hA h

Conclusion "
Well done!  This is the fact you will reach for most often when working with finite sets.

You have also been given one more fact about finite sets, which you will need later in
this world: `finite_empty` is a proof that the empty set is finite.  Both theorems are
listed in the `Finite` tab on the right.
"

/--
A set `S` is *finite* if it has only finitely many elements.  In Lean this is written
`S.Finite`, or `Set.Finite S`.

Note that `S.Finite` is a *statement*, just like `x ∈ S` or `A ⊆ B`: it is either true or
false, and it is something you prove.  In particular it is not a number — it does not
record *how many* elements `S` has, only that there are finitely many.
-/
DefinitionDoc Set.Finite as "Set.Finite"
NewDefinition Set.Finite

/--
A subset of a finite set is finite.

If `h : S.Finite` and `h2 : T ⊆ S`, then `Finite.subset h h2` is a proof that
`T.Finite`.  This can also be written `h.subset h2`.
-/
TheoremDoc Set.Finite.subset as "Set.Finite.subset" in "Finite"

/-- `finite_empty` is a proof that the empty set is finite. -/
TheoremDoc Set.finite_empty as "Set.finite_empty" in "Finite"

NewTheorem Set.Finite.subset Set.finite_empty
