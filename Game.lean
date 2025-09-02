-- From the Set theory game
import Game.Levels.Subset
import Game.Levels.Comp
import Game.Levels.Inter
import Game.Levels.Union
import Game.Levels.Combo
import Game.Levels.FamInter
import Game.Levels.FamUnion

-- Created by me
import Game.Levels.Functions
import Game.Levels.Spaces
import Game.Levels.Continuous
import Game.Levels.Empty

-- Here's what we'll put on the title screen
Title "The topology game"
Introduction
"
Welcome to the topology game!

In this game, you learn to work with topological spaces in Lean.

Some of the worlds in this game are from the Set Theory Game, created by Daniel J. Velleman.
"

Info "
In this game, you learn to work with topological spaces in Lean.

Some of the worlds in this game are from the Set Theory Game, created by Daniel J. Velleman.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

Dependency Intersection → Union
Dependency Union → Spaces
Dependency Continuous → Empty

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
