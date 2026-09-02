import Game.Levels.Compact.L02_compact_empty

open Set
namespace TTG

World "Compact"
Level 3
Title "Pick and choose"

Introduction "
In this level, we introduce a new tactic, `choose!`,
which will be useful when working with compact sets.

While `obtain` is a tactic to extract a witness from a statement of the form `∃ x, P x`,
`choose!` is a tactic to extract several witnesses from a statement of the form
`∀ y, ∃ x, P x y`.

The tactic `obtain` unpacks a single `∃` statement, while `choose!` unpacks many `∃`
statements at once.

Suppose you have a hypothesis `h : ∀ y, ∃ x, P x y`. Writing

```
choose! g hg using h
```

gives a function `g : Y → X` together with a proof `hg : ∀ y, P (g y) y`.

In this level, we apply `choose!` to prove that if a function is surjective, then it has a
right inverse.

(The assumption `[Nonempty X]` says that `X` has at least one element.  The tactic `choose!`
always builds a function defined on all of `Y`, so it needs somewhere to send the elements
it has no witness for.)
"

/-- If $f$ is a surjective function from a nonempty set, then $f$ has a right inverse. -/
Statement {X Y : Type} [Nonempty X] (f : X → Y) (h : ∀ y, ∃ x, f x = y) :
    ∃ g : Y → X, ∀ y, f (g y) = y := by
  Hint "Use `choose! g hg using {h}` to turn `{h}` into a function together with its
  defining property."
  choose! g hg using h
  Hint "Now `g` is the function you were asked for, so tell Lean to use it."
  Hint (hidden := true) "`use g` — and `{hg}` is already exactly the remaining goal."
  use g

Conclusion "
`choose!` also works when your hypothesis only says something for the elements of some set,
as in `h : ∀ y ∈ A, ∃ x, f x = y`.  You then get `hg : ∀ y ∈ A, f (g y) = y`: the function
is still defined on all of `Y`, but nothing is claimed about its values outside `A`.

You will use it in that form in the next level.
"

/--
If you have an assumption `h : ∀ x, ∃ y, P x y`, then `choose! g hg using h` introduces a
function `g` together with an assumption `hg : ∀ x, P x (g x)`.  In other words, it picks
such a `y` for every `x` at once, and names it `g x`.

It also works if the assumption only holds on a set, as in `h : ∀ x ∈ A, ∃ y, P x y`; then
`hg : ∀ x ∈ A, P x (g x)`.  Either way `g` is defined on the whole type, so `choose!`
needs the type of `y` to be nonempty — it has to send the remaining inputs somewhere.

Compare this with `obtain`, which unpacks a single `∃` statement.  Use `choose!` when you
need a witness for every element at once, not just for one.
-/
TacticDoc choose!
NewTactic choose!
