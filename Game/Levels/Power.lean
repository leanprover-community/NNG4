import Game.Levels.Multiplication
import Game.Levels.Power.L01zero_pow_zero
import Game.Levels.Power.L02zero_pow_succ
import Game.Levels.Power.L03pow_one
import Game.Levels.Power.L04one_pow
import Game.Levels.Power.L05pow_two
import Game.Levels.Power.L06pow_add
import Game.Levels.Power.L07mul_pow
import Game.Levels.Power.L08pow_pow
import Game.Levels.Power.L09add_sq
import Game.Levels.Power.L10FLT

World "Power"
Title "Power World"

Introduction
"
This world introduces exponentiation. If you want to define `37 ^ n`
then, as always, you will need to know what `37 ^ 0` is, and
what `37 ^ (succ d)` is, given only `37 ^ d`.

You can probably guess the names of the general theorems:

  * `pow_zero (a : ℕ) : a ^ 0 = 1`
  * `pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a`

Using only these, can you get past the final boss level?

The levels in this world were designed by Sian Carey, a UROP student
at Imperial College London, funded by a Mary Lister McCammon Fellowship
in the summer of 2019. Thanks to Sian and also thanks to Imperial
College for funding her.
"
