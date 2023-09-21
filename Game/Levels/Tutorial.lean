/- **TODO** need that brief apache2 and author string?
-/
import Game.Levels.Tutorial.L01rfl
import Game.Levels.Tutorial.L02rw
import Game.Levels.Tutorial.L03three_eq_sss0
import Game.Levels.Tutorial.L04add_zero
import Game.Levels.Tutorial.L05add_succ
import Game.Levels.Tutorial.L06twoaddone
import Game.Levels.Tutorial.L07twoaddtwo
/-!

# Tutorial world

This file defines Tutorial World. Like all worlds, this world
has a name, a title, an introduction, and most importantly
a finite set of levels (imported above). Each level has an
associated level number defined in it, and that's what determines
the order of the levels.
-/
World "Tutorial"
Title "Tutorial World"

Introduction
"In Tutorial World, you're going to learn how to prove theorems about numbers.
The boss level of this world is to prove that `2 + 2 = 4`.

You prove theorems like this using tools called *tactics*. Each
tactic performs a certain logical idea, and the puzzle is to
prove the theorem by applying the tactics in the right order.

Let's start by learning some basic tactics. Click on \"Start\" below to begin your quest.
"
