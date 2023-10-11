-- Here's the import to make Lean know about things called `Game`s
import GameServer.Commands

-- Here are the imports defining many worlds for the game `Game` (the natural number game,
-- in this case). Each world consists of a finite number of levels, and levels
-- are numbered 1,2,3,4... inside the level files.
import Game.Levels.Tutorial
import Game.Levels.Addition
import Game.Levels.Multiplication
import Game.Levels.Power
import Game.Levels.Implication
import Game.Levels.AdvAddition
--import Game.Levels.AdvMultiplication
--import Game.Levels.EvenOdd
--import Game.Levels.Inequality
--import Game.Levels.Prime
--import Game.Levels.StrongInduction
--import Game.Levels.Hard

-- Here's what we'll put on the title screen
Title "Natural Number Game"
Introduction
"
# Welcome to the Natural Number Game
#### An introduction to mathematical proof.

In this game, we will build the basic theory of the natural
numbers `{0,1,2,3,4,...}` from scratch. Our first goal is to prove
that `2 + 2 = 4`. Next we'll prove that `x + y = y + x`.
And at the end we'll see if we can prove Fermat's Last Theorem.
We'll do this by solving levels of a computer puzzle game called Lean.

# Read this.

Learning how to use an interactive theorem prover takes time.
Tests show that the people who get the most out of this game are
those who read the help texts like this one.

To start, click on \"Tutorial World\".

Note: this is a preliminary new Lean 4 version of the game; new versions
of inequality and advanced addition/multiplication worlds are in preparation.
Other brand new worlds will also be appearing during October 2023.

## More

Open \"Game Info\" in the burger menu on the top right for resources,
links, and ways to interact with the Lean community.
"

Info "
##### Game version: 4.1

#### Recent changes: rewrite of tutorial, addition, multiplication and power world.

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
* **Additional thanks:** All the student beta testers, all the schools
who invited Kevin to speak, and all the schoolkids who asked him questions
about the material.

## Resources

* The [Lean Zulip chat](https://leanprover.zulipchat.com/) forum
* [Original Lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) (no longer maintained)

## Problems?

Please ask any questions about this game in the
[Lean Zulip chat](https://leanprover.zulipchat.com/) forum, for example in
the stream \"New Members\". The community will happily help. Note that
the Lean Zulip chat is a professional research forum.
Please use your full real name there, stay on topic, and be nice. If you're
looking for somewhere less formal (e.g. you want to post natural number
game memes) then head on over to the [Lean Discord](https://discord.gg/WZ9bs9UCvx).

Alternatively, if you experience issues / bugs you can also open github issues:

* For issues with the game engine, please open an
[issue at the lean4game](https://github.com/leanprover-community/lean4game/issues) repo.
* For issues about the game's content, please open an
[issue at the NNG](https://github.com/hhu-adam/NNG4/issues) repo.

"

-- Here's where we show how to glue the worlds together
Dependency Addition → Multiplication → Power
--Dependency Addition → AdvAddition → AdvMultiplication → Inequality → Prime → Hard
--Dependency Multiplication → AdvMultiplication
--Dependency AdvAddition → EvenOdd → Inequality → StrongInduction
Dependency Addition → Implication → AdvAddition
MakeGame
