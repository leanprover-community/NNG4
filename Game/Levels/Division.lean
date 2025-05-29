import Game.Levels.Division.L01one_dvd
import Game.Levels.Division.L02dvd_refl
import Game.Levels.Division.L03dvd_zero
import Game.Levels.Division.L04dvd_one
import Game.Levels.Division.L05dvd_trans
import Game.Levels.Division.L06zero_dvd
import Game.Levels.Division.L07dvd_ls
import Game.Levels.Division.L08dvd_antisymm
import Game.Levels.Division.L09dvd_add
import Game.Levels.Division.L10dvd_mul_right.lean
import Game.Levels.Division.L11dvd_mul_both.lean
import Game.Levels.Division.L12dvd_not_eq.lean


World "Division"
Title "Division World"

Introduction
"
  This is the world in which we define `a ∣ b`. We will also prove
  standard facts about it. In particular, that it is a partial order.

  The definition of `a ∣ b` is that \"There exists a number `c` such
  that `b = c * a`\" So we will use tactics used to prove \"exists\"
  theorems.

  Click on \"Start\" to proceed.
"
