import Game.Levels.Tutorial.L01rfl
import Game.Levels.Tutorial.L02rw
import Game.Levels.Tutorial.L03three_eq_sss0
import Game.Levels.Tutorial.L04add_zero
import Game.Levels.Tutorial.L05add_zero2
import Game.Levels.Tutorial.L06add_succ
import Game.Levels.Tutorial.L07twoaddtwo
/-!

# Tutorial world

This file defines Tutorial World. Like all worlds, this world
has a name, a title, an introduction, and most importantly
a finite set of levels (imported above). Each level has a
level number defined within it, and that's what determines
the order of the levels.
-/
World "Tutorial"
Title "Tutorial World"

Introduction
"Welcome to tutorial world! In this world we learn the basics
of proving theorems. The boss level of this world
is the theorem `2 + 2 = 4`.

You prove theorems by solving puzzles using tools called *tactics*.
The aim is to prove the theorem by applying tactics
in the right order.

Let's learn some basic tactics. Click on \"Start\" below
to begin your quest.
"
