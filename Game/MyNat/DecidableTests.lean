import Game.MyNat.DecidableEq
import Game.MyNat.Power

example : 4 = 4 := by
  decide

example : 4 ≠ 5 := by
  decide

example : (0 : ℕ) + 0 = 0 := by
  decide

example : (2 : ℕ) + 2 = 4 := by
  decide

example : (2 : ℕ) + 2 ≠ 5 := by
  decide

example : (20 : ℕ) + 20 = 40 := by
  decide

example : (2 : ℕ) * 2 = 4 := by
  decide

example : (2 : ℕ) * 2 ≠ 5 := by
  decide

example : (3 : ℕ) ^ 2 ≠ 37 := by
  decide
