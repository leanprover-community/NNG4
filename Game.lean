import GameServer.Commands

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


--import Game.Levels.Inequality

Title "Natural Number Game"
Introduction
"
# Welcome to the Natural Number Game
#### A game which shows the power of induction

In this game, you get own version of the natural numbers, in an interactive
theorem prover called Lean. Your version of the natural numbers satisfies something called
the principle of mathematical induction, and a couple of other things too (Peano's axioms).
Unfortunately, nobody has proved any theorems about these
natural numbers yet! For example, addition will be defined for you,
but nobody has proved that `x + y = y + x` yet. This is your job. You're going to
prove mathematical theorems using the Lean theorem prover. In other words, you're going to solve
levels in a computer game.

You're going to prove these theorems using *tactics*. The introductory world, Tutorial World,
will take you through some of these tactics. During your proofs, the assistant shows your
\"goal\" (i.e. what you're supposed to be proving) and keeps track of the state of your proof.

Click on the blue \"Tutorial World\" to start your journey!

## More

Open the \"Game Info\" in the menu for resources, links, and infos about the game.
"

Info "
##### Game version: 4.0.2

## Progress saving

The game stores your progress in your local browser storage.
If you delete it, your progress will be lost!

Warning: In most browsers, deleting cookies will also clear the local storage
(or \"local site data\"). Make sure to download your game progress first!

## Credits

* **Creators:** Kevin Buzzard, […?], Jon Eugster
* **Original Lean3-version:** Kevin Buzzard, Mohammad Pedramfar
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot

## Resources

* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum
* [Original Lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)

## Problems?

Please ask any questions about this game in the
[Lean Zulip chat](https://leanprover.zulipchat.com/) forum, for example in
the stream \"New Members\". The community will happily help.

Alternatively, if you experience issues / bugs you can also open github issues:

* For issues with the game engine, please open an
[issue at the lean4game](https://github.com/leanprover-community/lean4game/issues) repo.
* For issues about the game's content, please open an
[issue at the NNG](https://github.com/hhu-adam/NNG4/issues) repo.

"

-- Add manual paths
Dependency Addition → Multiplication → Power
Dependency Addition → AdvAddition → AdvMultiplication → Inequality → Prime → Hard
Dependency Multiplication → AdvMultiplication
Dependency AdvAddition → EvenOdd → Inequality → StrongInduction

MakeGame
