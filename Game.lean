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
import Game.Levels.Connected

-- Here's what we'll put on the title screen
Title "The topology game"
Introduction
"
Welcome to the topology game!

In this game, you learn to work with topological spaces in Lean.

Open \"Game info\" in the \"≡\" menu in the top right corner for more for more information about this game.
"

Info "
In this game, you learn to work with topological spaces in Lean.

This game has been created by Bjørnar Gullikstad Hem ( bjornar.hem(at)epfl.ch ).
Feel free to contact me if you have any questions or suggestions.

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
Dependency FamInter → FamUnion
Dependency Continuous → Empty
Dependency Empty → Connected

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
