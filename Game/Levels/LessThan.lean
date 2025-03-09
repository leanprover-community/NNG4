import GameServer.Commands
import Game.Levels.LessThan.B_L01_succ_eq_succ_iff
import Game.Levels.LessThan.B_L02_succ_succ_eq_succ_succ_iff
import Game.Levels.LessThan.B_L03_lt_succ_self
import Game.Levels.LessThan.B_L04_not_lt_zero
import Game.Levels.LessThan.B_L05_lt_iff_le_not_le
import Game.Levels.LessThan.B_L06_lt_succ_iff_le
import Game.Levels.LessThan.B_L07_not_lt_and_lt_succ
import Game.Levels.LessThan.B_L08_strong_induction

World "LessThan"
Title "< World"

Introduction
"In this world we define `a < b` and prove standard
facts about it.  The final boss of this level is to prove the strong
induction principle.

If `a b` are natural number, We will eventually define `a < b` as `succ
a ≤ b`.  But first we have to introduce two new tactics.

Click on \"Start\" to proceed.
"
