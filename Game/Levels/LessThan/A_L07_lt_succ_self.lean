import Game.Levels.LessThan.A_L06_lt_trans

World "LessThan"
Level 7
Title "A number is (strictly) less than is own successor"

TheoremTab "<"

namespace MyNat

/-- `succ_le_succ x y` is a proof that if `succ x ≤ succ y` then `x ≤ y`. -/
TheoremDoc MyNat.lt_succ_self as "lt_succ_self" in "<"

Introduction ""

/-- a < a.succ -/
Statement lt_succ_self (a : ℕ) : a < a.succ  := by
  use 0
  have h1 := add_zero (succ a)
  exact h1.symm

Conclusion "Conclusion"
