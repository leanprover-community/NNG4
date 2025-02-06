import GameServer.Commands
import Game.Levels.LessThan.A_L01_lt_irrefl
import Game.Levels.LessThan.A_L02_ne_of_lt
import Game.Levels.LessThan.A_L03_not_lt_zero
import Game.Levels.LessThan.A_L04_lt_of_lt_of_le
import Game.Levels.LessThan.A_L05_lt_of_le_of_lt
import Game.Levels.LessThan.A_L06_lt_trans
import Game.Levels.LessThan.A_L07_lt_succ_self
import Game.Levels.LessThan.A_L08_succ_le_succ_iff
import Game.Levels.LessThan.A_L09_lt_succ_iff_le
import Game.Levels.LessThan.A_L10_lt_of_add_lt_add_left
import Game.Levels.LessThan.A_L11_add_lt_add_right
import Game.Levels.LessThan.A_L12_succ_lt_succ_iff
import Game.Levels.LessThan.A_L13_mul_le_mul_left
import Game.Levels.LessThan.A_L14_mul_lt_mul_of_pos_right
import Game.Levels.LessThan.A_L15_mul_lt_mul_of_pos_left
import Game.Levels.LessThan.A_L16_le_mul
import Game.Levels.LessThan.A_L17_pow_le
import Game.Levels.LessThan.A_L18_strong_induction

World "LessThan"
Title "< World"

Introduction
"
In this world we define `a < b` and prove standard facts
about it, such as \"if `a < b` and `b < c` then `a < c`.\"

The definition of `a < b` is `succ a ≤ b`.

Click on \"Start\" to proceed.
"
