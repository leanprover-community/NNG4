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
a finite set of levels (imported above). Each level has a weighting
and this determines the order of the levels.
-/
World "Tutorial"
Title "Tutorial World"

Introduction
"
In this world we introduce two basic tactics (`rfl` and `rw`).
We also introduce several mathematical concepts: the (natural) numbers `ℕ`,
explicit examples of numbers such as 0 and 3, and addition of two numbers.
The final boss is to prove that `2 + 2 = 4`. Good luck!

Click on \"Next\" to begin your quest.
"
