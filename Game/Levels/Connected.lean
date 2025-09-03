import Game.Levels.Connected.L01_preconnected

World "Connected"
Title "Connected sets"

Introduction
"
This module introduces the basics of connected sets in topology.

In lean, a set `U` in a topological space `X` is _preconnected_ if,
for any two open sets `V` and `W` in `X`  such that
`U ⊆ V ∪ W`, `U ∩ V ≠ ∅` and `U ∩ W ≠ ∅`,
we have that `U ∩ (V ∩ W) ≠ ∅`.

A set `U ⊆ X` is _connected_ if it is preconnected and nonempty.
"
