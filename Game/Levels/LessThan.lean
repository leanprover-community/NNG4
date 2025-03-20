import GameServer.Commands
import Game.Levels.LessThan.L01_succ_eq_succ_iff
import Game.Levels.LessThan.L02_succ_succ_eq_succ_succ_iff
import Game.Levels.LessThan.L03_lt_succ_self
import Game.Levels.LessThan.L04_le_iff_lt_or_eq
import Game.Levels.LessThan.L05_not_lt_zero
import Game.Levels.LessThan.L06_lt_iff_le_not_le
import Game.Levels.LessThan.L07_lt_succ_iff_le
import Game.Levels.LessThan.L08_not_lt_and_lt_succ
import Game.Levels.LessThan.L09_strong_induction

World "LessThan"
Title "< World"

Introduction
"In this world we define `a < b` and prove standard
facts about it.  The final boss of this level is to prove the strong
induction principle.

In this level we will define the proposition `a < b` as `succ a ≤ b`.
We will define \"less than\" in terms of \"less than or equal\".  At
first glance, this may seem like a circular definition but it is not.

Before we prove this and other facts about \"less than\", we need to
introduce two new tactics.

Click on \"Start\" to proceed.
"
