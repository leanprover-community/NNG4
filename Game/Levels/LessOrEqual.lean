import GameServer.Commands
import Game.Levels.LessOrEqual.L01le_refl
import Game.Levels.LessOrEqual.L02zero_le
import Game.Levels.LessOrEqual.L03le_succ_self
import Game.Levels.LessOrEqual.L04le_trans
import Game.Levels.LessOrEqual.L05le_zero
import Game.Levels.LessOrEqual.L06le_antisymm
import Game.Levels.LessOrEqual.L07or_symm
import Game.Levels.LessOrEqual.L08le_total

World "LessOrEqual"
Title "≤ World"

Introduction
"
In this world we define `a ≤ b` and prove standard facts
about it, such as \"if `a ≤ b` and `b ≤ c` then `a ≤ c`.\"

The definition of `a ≤ b` is \"there exists a number `c`
such that `b = a + c`. \" So we're going to have to learn
a tactic to prove \"exists\" theorems, and another one
to use \"exists\" hypotheses.

Click on \"Start\" to proceed.
"
