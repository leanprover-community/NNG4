import Game.Levels.Addition.L01zero_add
import Game.Levels.Addition.L02succ_add
import Game.Levels.Addition.L03add_comm
import Game.Levels.Addition.L04add_assoc
import Game.Levels.Addition.L05add_right_comm

World "Addition"
Title "Addition World"

Introduction
"
Welcome to Addition World! In this world we'll learn the `induction` tactic.
This will enable us to defeat the boss level of this world, namely `x + y = y + x`.

The tactics `rw`, `rfl` and `induction` are the only tactics you'll need to
beat all the levels in Addition World, Multiplication World, and Power World.
Power World contains the final boss of the game.
"

-- **TODO** put this comment back
-- There are plenty more tactics in this game, but you'll only need to know them if you
-- want to explore the game further (for example if you decide to 100%
-- the game).
-- "
