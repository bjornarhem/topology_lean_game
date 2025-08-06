import Game.Levels.Functions
import Game.Levels.Spaces

-- Here's what we'll put on the title screen
Title "The topology game"
Introduction
"
Welcome to the topology game!
"

Info "
In this game, you learn to work with topological spaces in Lean.

Before playing this game, it is recommended to have at least some knowledge of Lean tactics and sets in Lean.
You can learn this, for example, by playing the first worlds in the Set Theory Game.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
