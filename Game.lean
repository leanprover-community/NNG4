-- Here's the import to make Lean know about things called `Game`s
import GameServer.Commands

-- Here are the imports defining many worlds for the game `Game`.
-- Each world consists of a finite totally ordered set of levels.
import Game.Levels.Tutorial
import Game.Levels.Addition
import Game.Levels.Multiplication
import Game.Levels.Power
import Game.Levels.AdvAddition
import Game.Levels.AdvMultiplication
import Game.Levels.EvenOdd
import Game.Levels.Inequality
import Game.Levels.Prime
import Game.Levels.StrongInduction
import Game.Levels.Hard

-- Here's what we'll put on the title screen
Title "Natural Number Game"
Introduction
"
# Welcome to the Natural Number Game
#### An introduction to the concept of a mathematical proof.

In this game, we will define the natural numbers `{0,1,2,3,4,…}`
from scratch, and then build up their theory. For example
we will prove that `2 + 2 = 4`, and later on we will prove
that `x + y = y + x`. We will do this by solving levels of a computer
puzzle game called `Lean`.

Click on the blue \"Tutorial World\" to learn what these puzzles
look like, and how to solve them.

## More

Open the \"Game Info\" in the menu (in the burger on the right, **TODO** at least on port 3000) for resources, links, and more information about the game.
"

Info "
##### Game version: 4.1

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!

## Credits

* **Creators:** Kevin Buzzard, Jon Eugster
* **Original Lean3-version:** Kevin Buzzard, Mohammad Pedramfar
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot
* **Additional levels:** Sian Carey, Ivan Farabella, Archie Browne.

## Resources

* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum
* [Original Lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) (no longer maintained)

## Problems?

Please ask any questions about this game in the
[Lean Zulip chat](https://leanprover.zulipchat.com/) forum, for example in
the stream \"New Members\". The community will happily help. This is a professional research forum. Please use your full real name there, stay on topic, and be nice.

Alternatively, if you experience issues / bugs you can also open github issues:

* For issues with the game engine, please open an
[issue at the lean4game](https://github.com/leanprover-community/lean4game/issues) repo.
* For issues about the game's content, please open an
[issue at the NNG](https://github.com/hhu-adam/NNG4/issues) repo.

"

-- Here's where we show how to glue the worlds together
Dependency Addition → Multiplication → Power
Dependency Addition → AdvAddition → AdvMultiplication → Inequality → Prime → Hard
Dependency Multiplication → AdvMultiplication
Dependency AdvAddition → EvenOdd → Inequality → StrongInduction

MakeGame
